// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:56 PST by lamport
//      modified on Thu Jan 10 11:22:26 PST 2002 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.atomic.LongAdder;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.SimulationWorker.SimulationWorkerError;
import tlc2.tool.SimulationWorker.SimulationWorkerResult;
import tlc2.tool.coverage.CostModelCreator;
import tlc2.tool.impl.Tool;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.liveness.LiveCheck1;
import tlc2.tool.liveness.LiveException;
import tlc2.tool.liveness.NoOpLiveCheck;
import tlc2.util.RandomGenerator;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.value.IValue;
import util.FileUtil;
import util.FilenameToStream;

public class Simulator {

	public static boolean EXPERIMENTAL_LIVENESS_SIMULATION = Boolean
			.getBoolean(Simulator.class.getName() + ".experimentalLiveness");

	/* Constructors */
	/**
	 * SZ Feb 20, 2009: added the possibility to pass the SpecObject, this is
	 * compatibility constructor
	 * 
	 * @throws IOException
	 */
	public Simulator(String specFile, String configFile, String traceFile, boolean deadlock, int traceDepth,
			long traceNum, RandomGenerator rng, long seed, boolean preprocess, FilenameToStream resolver)
			throws IOException {
		// Default to 1 worker thread if not specified.
		this(specFile, configFile, traceFile, deadlock, traceDepth, traceNum, rng, seed, preprocess, resolver, 1);
	}

	// SZ Feb 20, 2009: added the possibility to pass the SpecObject
	public Simulator(String specFile, String configFile, String traceFile, boolean deadlock, int traceDepth,
			long traceNum, RandomGenerator rng, long seed, boolean preprocess, FilenameToStream resolver,
			int numWorkers) throws IOException {
		int lastSep = specFile.lastIndexOf(FileUtil.separatorChar);
		String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep + 1);
		specFile = specFile.substring(lastSep + 1);

		// SZ Feb 24, 2009: setup the user directory
		// SZ Mar 5, 2009: removed it again because of the bug in simulator
		// ToolIO.setUserDir(specDir);

		this.tool = new Tool(specDir, specFile, configFile, resolver);
		this.tool.init(preprocess, null); // parse and process the spec

		this.checkDeadlock = deadlock;
		this.checkLiveness = !this.tool.livenessIsTrue();
		this.invariants = this.tool.getInvariants();
		if (traceDepth != -1) {
			// this.actionTrace = new Action[traceDepth]; // SZ: never read
			// locally
			this.traceDepth = traceDepth;
		} else {
			// this.actionTrace = new Action[0]; // SZ: never read locally
			this.traceDepth = Long.MAX_VALUE;
		}
		this.traceFile = traceFile;
		this.traceNum = traceNum;
		this.rng = rng;
		this.seed = seed;
		this.aril = 0;
		this.numWorkers = numWorkers;
		// Initialization for liveness checking
		if (this.checkLiveness) {
			if (EXPERIMENTAL_LIVENESS_SIMULATION) {
				final String tmpDir = System.getProperty("java.io.tmpdir");
				liveCheck = new LiveCheck(this.tool, new Action[0], tmpDir, new DummyBucketStatistics());
			} else {
				liveCheck = new LiveCheck1(this.tool);
			}
		} else {
			liveCheck = new NoOpLiveCheck(tool, specDir);
		}

		if (TLCGlobals.isCoverageEnabled()) {
        	CostModelCreator.create(this.tool);
        }
	}

	/* Fields */
	private final ILiveCheck liveCheck;
	private final ITool tool;
	private final Action[] invariants; // the invariants to be checked
	private final boolean checkDeadlock; // check deadlock?
	private final boolean checkLiveness; // check liveness?

	// The total number of states/traces generated by all workers. May be written to
	// concurrently, so we use a LongAdder to reduce potential contention.
	private final LongAdder numOfGenStates = new LongAdder();
	private final LongAdder numOfGenTraces = new LongAdder();

	// private Action[] actionTrace; // SZ: never read locally
	private final String traceFile;

	// The maximum length of a simulated trace.
	private final long traceDepth;

	// The maximum number of total traces to generate.
	private final long traceNum;

	// The number of worker threads to use for simulation.
	private int numWorkers = 1;

	private final RandomGenerator rng;
	private final long seed;
	private long aril;
	private IValue[] localValues = new IValue[4];

	// The set of all initial states for the given spec. This should be only be
	// computed once and re-used whenever a new random trace is generated. This
	// variable should not be written to concurrently, but is allowed to be read
	// concurrently.
	private StateVec initStates = new StateVec(0);

	// Each simulation worker pushes their results onto this shared queue.
	private BlockingQueue<SimulationWorkerResult> workerResultQueue = new LinkedBlockingQueue<>();
		 
	 /**
	 * Returns whether a given error code is considered "continuable". That is, if
	 * any worker returns this error, should we consider continuing to run the
	 * simulator. These errors are considered "fatal" since they most likely
	 * indicate an error in the way the spec is written.
	 */
	private boolean isNonContinuableError(int ec) {
		return ec == EC.TLC_INVARIANT_EVALUATION_FAILED || 
			   ec == EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED ||
			   ec == EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT;
	}
	
	/**
	 * Shut down all of the given workers and make sure they have stopped.
	 */
	private void shutdownAndJoinWorkers(final List<SimulationWorker> workers) throws InterruptedException {
		for (SimulationWorker worker : workers) {
			worker.interrupt();
			worker.join();
		}
	}

	/*
	 * This method does random simulation on a TLA+ spec.
	 * 
	 * It runs until en error is encountered or we have generated the maximum number of traces.
	 */
	public void simulate() throws Exception {
		TLCState curState = null;

		//
		// Compute the initial states.
		//
		try {

			// The init states are calculated only ever once and never change
			// in the loops below. Ideally the variable would be final.
			this.initStates = this.tool.getInitStates();

			// This counter should always be initialized at zero.
			assert (this.numOfGenStates.longValue() == 0);
			this.numOfGenStates.add(this.initStates.size());
			
			MP.printMessage(EC.TLC_COMPUTING_INIT_PROGRESS, this.numOfGenStates.toString());

			// Check all initial states for validity.
			for (int i = 0; i < this.initStates.size(); i++) {
				curState = this.initStates.elementAt(i);
				if (this.tool.isGoodState(curState)) {
					for (int j = 0; j < this.invariants.length; j++) {
						if (!this.tool.isValid(this.invariants[j], curState)) {
							// We get here because of invariant violation.
							MP.printError(EC.TLC_INVARIANT_VIOLATED_INITIAL,
									new String[] { this.tool.getInvNames()[j], curState.toString() });
							return;
						}
					}
				} else {
					MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL, curState.toString());
					return;
				}
			}
		} catch (Exception e) {
			if (curState != null) {
				MP.printError(EC.TLC_INITIAL_STATE,
						new String[] { (e.getMessage() == null) ? e.toString() : e.getMessage(), curState.toString() });
			} else {
				MP.printError(EC.GENERAL, e); // LL changed call 7 April 2012
			}

			this.printSummary();
			return;
		}

		if (this.numOfGenStates.longValue() == 0) {
			MP.printError(EC.TLC_NO_STATES_SATISFYING_INIT);
			return;
		}

		// It appears deepNormalize brings the states into a canonical form to
		// speed up equality checks.
		this.initStates.deepNormalize();

		//
		// Start progress report thread.
		//
		final ProgressReport report = new ProgressReport();
		report.start();

		//
		// Start simulating.
		//
		this.aril = rng.getAril();
		
		// Start up multiple simulation worker threads, each with their own unique seed.
		final List<SimulationWorker> workers = new ArrayList<>();
		final Set<Integer> runningWorkers = new HashSet<>();
		for (int i = 0; i < this.numWorkers; i++) {			
			final SimulationWorker worker = new SimulationWorker(i, this.tool, initStates, this.workerResultQueue,
					this.rng.nextLong(), this.traceDepth, this.traceNum, this.checkDeadlock, this.traceFile,
					this.liveCheck, this.numOfGenStates, this.numOfGenTraces);		

			worker.start();
			workers.add(worker);
			runningWorkers.add(i);
		}
		
		// Continuously consume results from all worker threads.
		while (true) {
			final SimulationWorkerResult result = workerResultQueue.take();

			// If the result is an error, print it.
			if (result.isError()) {
				SimulationWorkerError error = result.error();
				
				// We assume that if a worker threw an unexpected exception, there is a bug
				// somewhere, so we print out the exception and terminate. In the case of a
				// liveness error, which is reported as an exception, we also terminate.
				if (error.exception != null) {
					if (error.exception instanceof LiveException) {
						// In case of a liveness error, there is no need to print out
						// the behavior since the liveness checker should take care of that itself.
						this.printSummary();
					} else {
						printBehavior(EC.GENERAL, new String[] { MP.ECGeneralMsg("", error.exception) }, error.state,
								error.stateTrace);
					}
					break;
				}
				
				// Print the trace for all other errors.
				printBehavior(error);
				
				// For certain, "fatal" errors, we shut down all workers and terminate,
				// regardless of the "continue" parameter, since these errors likely indicate a bug in the spec.
				if (isNonContinuableError(error.errorCode)) {
					break;
				}
				
				// If the 'continue' option is false, then we always terminate on the
				// first error, shutting down all workers. Otherwise, we continue receiving
				// results from the worker threads.
				if (!TLCGlobals.continuation) {
					break;
				}
			} 
			// If the result is OK, this indicates that the worker has terminated, so we
			// make note of this. If all of the workers have terminated, there is no need to
			// continue waiting for results, so we should terminate.
			else {
				runningWorkers.remove(result.workerId());
				if(runningWorkers.isEmpty()) {
					break;
				}
			}
		}
		
		// Shut down all workers.
		this.shutdownAndJoinWorkers(workers);

		// Do a final progress report.
		report.isRunning = false;
		synchronized (report) {
			report.notify();
		}
		// Wait for the progress reporter thread to finish.
		report.join();
	}

	public final void printBehavior(SimulationWorkerError error) {
		printBehavior(error.errorCode, error.parameters, error.state, error.stateTrace);
	}

	/**
	 * Prints out the simulation behavior, in case of an error. (unless we're at
	 * maximum depth, in which case don't!)
	 */
	public final void printBehavior(final int errorCode, final String[] parameters, final TLCState state, final StateVec stateTrace) {
		MP.printError(errorCode, parameters);
		if (this.traceDepth == Long.MAX_VALUE) {
			MP.printMessage(EC.TLC_ERROR_STATE);
			StatePrinter.printState(state);
		} else {
			MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
			TLCState lastState = null;
			for (int i = 0; i < stateTrace.size(); i++) {
				StatePrinter.printState(stateTrace.elementAt(i), lastState, i + 1);
				lastState = stateTrace.elementAt(i);
			}
			StatePrinter.printState(state, null, stateTrace.size() + 1);
		}
		this.printSummary();
	}

	public IValue getLocalValue(int idx) {
		if (idx < this.localValues.length) {
			return this.localValues[idx];
		}
		return null;
	}

	public void setLocalValue(int idx, IValue val) {
		if (idx >= this.localValues.length) {
			IValue[] vals = new IValue[idx + 1];
			System.arraycopy(this.localValues, 0, vals, 0, this.localValues.length);
			this.localValues = vals;
		}
		this.localValues[idx] = val;
	}

	/**
	 * Prints the summary
	 */
	public final void printSummary() {
		this.reportCoverage();

		/*
		 * This allows the toolbox to easily display the last set of state space
		 * statistics by putting them in the same form as all other progress statistics.
		 */
		if (TLCGlobals.tool) {
			MP.printMessage(EC.TLC_PROGRESS_SIMU, String.valueOf(numOfGenStates.longValue()));
		}

		MP.printMessage(EC.TLC_STATS_SIMU, new String[] { String.valueOf(numOfGenStates.longValue()),
				String.valueOf(this.seed), String.valueOf(this.aril) });
	}

	/**
	 * Reports coverage
	 */
	public final void reportCoverage() {
		if (TLCGlobals.isCoverageEnabled()) {
            CostModelCreator.report(this.tool);
		}
	}

	/**
	 * Reports progress information
	 */
	final class ProgressReport extends Thread {

		volatile boolean isRunning = true;

		public void run() {
			int count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
			try {
				while (isRunning) {
					synchronized (this) {
						this.wait(TLCGlobals.progressInterval);
					}
					MP.printMessage(EC.TLC_PROGRESS_SIMU, String.valueOf(numOfGenStates.longValue()));
					if (count > 1) {
						count--;
					} else {
						reportCoverage();
						count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
					}
				}
			} catch (Exception e) {
				// SZ Jul 10, 2009: changed from error to bug
				MP.printTLCBug(EC.TLC_REPORTER_DIED, null);
			}
		}
	}
}
