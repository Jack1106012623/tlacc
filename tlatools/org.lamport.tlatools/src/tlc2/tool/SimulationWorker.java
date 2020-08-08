/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   William Schultz - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import java.io.PrintWriter;
import java.util.Optional;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.LongAdder;

import tlc2.output.EC;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.util.IdThread;
import tlc2.util.RandomGenerator;
import util.FileUtil;

/**
 * A SimulationWorker repeatedly checks random traces of a spec.
 * 
 * It is constructed with an initial seed which it uses to initialize its
 * internal random number generator. A simulation worker continually generates
 * random traces, even if it encounters errors of any kind i.e.
 * invariant/liveness violations, evaluation errors, etc. A worker communicates
 * these errors by pushing its results onto a result queue, that is provided to
 * it at construction time.
 * 
 * Workers may terminate in two possible ways. They will terminate if they
 * receive an "interruption" signal, and they will terminate if they reach their
 * maximum trace count limit. Otherwise, they will continue to run forever,
 * generating new traces. It is the job of an external thread/client to
 * determine if the errors produced are cause for termination or can be ignored.
 * 
 * Upon termination due to any cause, a worker thread will always push a final
 * OK result onto its result queue. This acts as a way to signal external
 * clients that this thread has terminated.
 */
public class SimulationWorker extends IdThread {
	
	// This worker's local source of randomness.
	private final RandomGenerator localRng;

	// The state currently being processed.
	TLCState curState;

	// Stores a trace generated by this worker.
	private final StateVec stateTrace;
	
	// The set of initial states for the spec. 
	private StateVec initStates;
	
	// The queue that the worker places its results onto.
	private final BlockingQueue<SimulationWorkerResult> resultQueue;
	
	// Tracks the number of traces that have been generated so far.
	private int traceCnt = 0;
	
	// The maximum number of traces this worker should generate before terminating.
	private final long maxTraceNum;
	
	// The maximum length of any generated trace.
	private final int maxTraceDepth;
	
	// Should this worker check traces for deadlock.
	private final boolean checkDeadlock;
	
	// The base name of the file that this worker writes out generated traces to. If it is null,
	// no trace files are generated.
	private final String traceFile;
	
	// A counter that tracks the number of generated states/traces. This counter may be
	// shared among workers, so its count may be greater than the number of states/traces
	// generated by this worker alone. It is the duty of this worker, though, to
	// update it whenever it generates a new state or trace.
	private final LongAdder numOfGenStates;
	private final LongAdder numOfGenTraces;
	private final LongAdder sumLengthOfGenTraces;

	private final ITool tool;
	private final ILiveCheck liveCheck;	
	
	// Adjacency Matrix with link weights.
	final long[][] actionStats;
	
	/**
	 * Encapsulates information about an error produced by a simulation worker.
	 */
	 public static class SimulationWorkerError {
		
		public SimulationWorkerError(int errorCode, String[] parameters, TLCState state, StateVec stateTrace,
				Exception e) {
			this.errorCode = errorCode;
			this.parameters = parameters;
			this.state = state;
			// Take of copy of the worker's stateTrace because this worker will concurrently
			// modify its stateTrace (by generating more behaviors) when Simulator iterates
			// (its copy of) stateTrace to print this error.
			this.stateTrace = new StateVec(stateTrace);
			this.exception = e;
		}
		
		// The error code to report.
		public final int errorCode;

		// Any additional information to be included in a reported error string.
		public final String[] parameters;

		// The TLC state associated with the error.
		public final TLCState state;

		// The TLC trace associated with the error.
		public final StateVec stateTrace;

		// An exception associated with the error.
		public final Exception exception;
	}
	
	
	/**
	 * Encapsulates information about a result produced by a simulation worker.
	 * 
	 * A result can either be an error or OK (indicating no error). Each result is
	 * associated with a specific worker.
	 */
	public static class SimulationWorkerResult {
		
		/**
		 * Constructs an OK result.
		 */
		static SimulationWorkerResult OK(int workerId) {
			SimulationWorkerResult res = new SimulationWorkerResult();
			res.workerId = workerId;
			return res;
		}
			
		/**
		 * Constructs an error result.
		 */
		static SimulationWorkerResult Error(int workerId, SimulationWorkerError err) {
			SimulationWorkerResult res = new SimulationWorkerResult();
			res.error = Optional.of(err);
			res.workerId = workerId;
			return res;
		}

		/**
		 * Returns whether this result is an error.
		 */
		public boolean isError() {
			return error.isPresent();
		}
		
		/**
		 * Returns the error for this result. Only valid to call if an error is present.
		 */
		public SimulationWorkerError error() {
			return error.get();
		}
		
		public int workerId() {
			return workerId;
		}
		
		private int workerId; // The worker that generated this result.
		private Optional<SimulationWorkerError> error = Optional.empty();

	}
	
	public SimulationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue,
			long seed, int maxTraceDepth, long maxTraceNum, boolean checkDeadlock, String traceFile,
			ILiveCheck liveCheck) {
		this(id, tool, resultQueue, seed, maxTraceDepth, maxTraceNum, checkDeadlock, traceFile, liveCheck,
				new LongAdder(), new LongAdder(), new LongAdder());
	}

	public SimulationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue,
			long seed, int maxTraceDepth, long maxTraceNum, boolean checkDeadlock, String traceFile,
			ILiveCheck liveCheck, LongAdder numOfGenStates, LongAdder numOfGenTraces, LongAdder sumLengthLongAdder) {
		super(id);
		this.localRng = new RandomGenerator(seed);
		this.tool = tool;
		this.maxTraceDepth = maxTraceDepth;
		this.maxTraceNum = maxTraceNum;
		this.resultQueue = resultQueue;
		this.checkDeadlock = checkDeadlock;
		this.traceFile = traceFile;
		this.liveCheck = liveCheck;
		this.numOfGenStates = numOfGenStates;
		this.numOfGenTraces = numOfGenTraces;
		this.sumLengthOfGenTraces = sumLengthLongAdder;
		this.stateTrace = new StateVec(maxTraceDepth);
		
		if (TLCState.Empty instanceof TLCStateMutSimulation) {
			final Action[] actions = this.tool.getActions();
			final int len = actions.length;
			this.actionStats = new long[len][len];
		} else {
			// Write all statistics into a single cell that we will ignore.
			this.actionStats = new long[1][1];
		}
	}
	
	/**
	 * The main worker loop. Continually generates random traces until the trace count limit
	 * is reached or until the worker is interrupted.
	 * 
	 * We use the standard Java notion of thread "interruption" as a mechanism for
	 * halting/cancelling the execution of a worker thread. There's nothing particularly
	 * special about this. The Thread.interrupt() just sets a boolean flag that the
	 * running thread then periodically checks via calls to Thread.interrupted(). We could
	 * implement this manually but it's simpler to use the built-in mechanism.
	 */
	public final void run() {
		while(true) {
			try {
				// The trace simulation method should do appropriately frequent interruption
				// checks.
				final Optional<SimulationWorkerError> res = simulateRandomTrace();
				traceCnt++;
				this.numOfGenTraces.increment();

				// If we have an error result, place it on the output queue.
				if (res.isPresent()) {
					final SimulationWorkerError err = res.get();
					resultQueue.put(SimulationWorkerResult.Error(this.myGetId(), err));
					// One would assume to return from this branch to stop the worker from creating
					// additional behaviors. However, this is at the discretion of Simulator, which
					// checks if the user ran simulation with "-continue".  If not, Simulator
					// will signal termination asynchronously.
				}

				// Abide by the maximum trace generation count.
				if (traceCnt >= maxTraceNum) {
					resultQueue.put(SimulationWorkerResult.OK(this.myGetId()));
					return;
				}
			} catch (final InterruptedException e) {
				// Gracefully terminate if we were interrupted.
				resultQueue.offer(SimulationWorkerResult.OK(this.myGetId()));
				return;
			} catch (final Exception e) {
				final SimulationWorkerError err = new SimulationWorkerError(0, null, this.curState, this.stateTrace, e);
				resultQueue.offer(SimulationWorkerResult.Error(this.myGetId(), err));
				return;
			}	
		}
	}

	/**
	 * Check to see if the worker thread has been interrupted.
	 */
	private void checkForInterrupt() throws InterruptedException {
		if (Thread.interrupted()) {
			throw new InterruptedException();
		}
	}
	
	/**
	 * This method returns a state that is randomly chosen from the set of states.
	 * It returns null if the set of states is empty.
	 */
	private final TLCState randomState(RandomGenerator rng, StateVec states) throws EvalException {
		final int len = states.size();
		if (len > 0) {
			final int index = (int) Math.floor(rng.nextDouble() * len);
			return states.elementAt(index);
		}
		return null;
	}

	/**
	 * Generates a single random trace.
	 *
	 * The core steps of this process are as follows:
	 * 
	 *  a) Pick one of the initial states. 
	 *  b) Randomly pick an action to generate the successor states (more than 1) to the current initial state. 
	 *  c) Check all of the generated successors for their validity. 
	 *  d) Randomly pick a generated successor and make it the new current state.
	 *
	 * Returns an Optional error representing the outcome of the trace generation. If the trace generation produced no error,
	 * returns Optional.empty().
	 *
	 */
	private Optional<SimulationWorkerError> simulateRandomTrace() throws Exception {
		// TODO With the introduction of TLCStateMutSimulation, stateTrace could be
		// eliminated and the predecessor state stored as a reference in its successor
		// (linked list of states). It would also be advantageous if "-depth N" is >>
		// than the actual average trace length, in which case we allocate a way too
		// large stateTrace.
		stateTrace.clear();

		// a) Randomly select a state from the set of init states.
		curState = randomState(this.localRng, initStates);
		setCurrentState(curState);
		
		boolean inConstraints = tool.isInModel(curState);
		
		final Action[] actions = this.tool.getActions();
		final int len = actions.length;

		// Simulate a trace up to the maximum specified length.
		for (int traceIdx = 0; traceIdx < maxTraceDepth; traceIdx++) {
			// We don't want this thread to run for too long without checking for
			// interruption, so we do so on every iteration of the main trace generation
			// loop.
			checkForInterrupt();

			// Add the curState to the trace regardless of its inModel property.
			stateTrace.addElement(curState);

			// Make sure this state satisfies the model constraints.
			if (!inConstraints) {
				break;
			}

			// b) Get the current state's successor states.
			StateVec nextStates = null;
			int index = (int) Math.floor(this.localRng.nextDouble() * len);
			final int p = this.localRng.nextPrime();
			for (int i = 0; i < len; i++) {
				nextStates = this.tool.getNextStates(actions[index], curState);
				if (!nextStates.empty()) {
					break;
				}
				index = (index + p) % len;
			}
			if (nextStates == null || nextStates.empty()) {
				if (checkDeadlock) {
					// We get here because of deadlock.
					return Optional.of(new SimulationWorkerError(EC.TLC_DEADLOCK_REACHED, null, curState, stateTrace, null));
				}
				break;
			}

			// c) Check all generated next states before all but one are discarded.
			for (int i = 0; i < nextStates.size(); i++) {
				numOfGenStates.increment();
				final TLCState state = nextStates.elementAt(i);
				// Any check below may terminate simulation, which then makes state the final
				// state in the trace. To correctly print its state number, it needs to know its
				// predecessor.
				state.setPredecessor(curState);

				if (!tool.isGoodState(state)) {
					return Optional.of(new SimulationWorkerError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT, null, state,
							stateTrace, null));
				}

				// Check invariants.
				int idx = 0;
				try {
					for (idx = 0; idx < this.tool.getInvariants().length; idx++) {
						if (!tool.isValid(this.tool.getInvariants()[idx], state)) {
							// We get here because of an invariant violation.
							return Optional.of(new SimulationWorkerError(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
									new String[] { tool.getInvNames()[idx] }, state, stateTrace, null));
						}
					}
				} catch (final Exception e) {
					return Optional.of(new SimulationWorkerError(EC.TLC_INVARIANT_EVALUATION_FAILED,
							new String[] { tool.getInvNames()[idx], e.getMessage() }, state, stateTrace, null));
				}

				// Check action properties.
				try {
					for (idx = 0; idx < this.tool.getImpliedActions().length; idx++) {
						if (!tool.isValid(this.tool.getImpliedActions()[idx], curState, state)) {
							// We get here because of implied-action violation.
							return Optional.of(new SimulationWorkerError(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
									new String[] { tool.getImpliedActNames()[idx] }, state, stateTrace, null));
						}
					}
				} catch (final Exception e) {
					return Optional.of(new SimulationWorkerError(EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED,
							new String[] { tool.getImpliedActNames()[idx], e.getMessage() }, state, stateTrace, null));
				}

			}

			// At this point all generated successor states have been checked for
			// their respective validity (isGood/isValid/impliedActions/...).

			// d) Randomly select one of them and make it the current state for the next
			// iteration of the loop.
			final TLCState s1 = randomState(localRng, nextStates);
			inConstraints = (tool.isInModel(s1) && tool.isInActions(curState, s1));
			s1.setPredecessor(curState); // Should be redundant but let's be safe anyway.
			s1.setActionId(index);
			// In case actionStats are off, we waste a few cycles to increment this counter
			// nobody is going to look at.
			this.actionStats[curState.getActionId()][s1.getActionId()]++;
			curState = s1;
			setCurrentState(curState);
		}

		// Check for interruption once more before entering liveness checking.
		checkForInterrupt();

		// Check if the current trace satisfies liveness properties.
		liveCheck.checkTrace(tool, stateTrace);
		
		final int traceLength = stateTrace.size();
		this.sumLengthOfGenTraces.add(traceLength);
		
		// Write the trace out if desired. The trace is printed in the
		// format of TLA module, so that it can be read by TLC again.
		if (traceFile != null) {
			// Make sure each worker outputs to its own set of trace files.
			final String fileName = traceFile + "_" + String.valueOf(this.myGetId()) + "_" + this.traceCnt;
			// TODO is it ok here?
			final PrintWriter pw = new PrintWriter(FileUtil.newBFOS(fileName));
			pw.println("---------------- MODULE " + fileName + " -----------------");
			for (int idx = 0; idx < stateTrace.size(); idx++) {
				pw.println("STATE_" + (idx + 1) + " == ");
				pw.println(stateTrace.elementAt(idx) + "\n");
			}
			pw.println("=================================================");
			pw.close();
		}

		// Finished trace generation without any errors.
		return Optional.empty();
	}
	
	public final int getTraceCnt() {
		return this.traceCnt + 1; // +1 to account the currently generated behavior. 
	}
	
	public final StateVec getTrace() {
		return stateTrace;
	}

	public void start(StateVec initStates) {
		this.initStates = initStates;
		this.start();
	}
}