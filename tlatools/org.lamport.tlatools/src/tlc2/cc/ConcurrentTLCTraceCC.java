package tlc2.cc;

import java.io.IOException;
import java.util.List;
import java.util.Random;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.ConcurrentTLCTrace;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.TraceApp;
import tlc2.tool.ConcurrentTLCTrace.Record;
import tlc2.value.RandomEnumerableValues;

public class ConcurrentTLCTraceCC extends ConcurrentTLCTrace {

	public ConcurrentTLCTraceCC(String metadir, String specFile, TraceApp tool) throws IOException {
		super(metadir, specFile, tool);
		// TODO Auto-generated constructor stub
	}
	@Override
	protected final TLCStateInfo[] getTrace(TLCStateInfo sinfo, final List<Record> records) {
		// Re-Initialize the rng with the seed value recorded and used during the model
		// checking phase. Otherwise, we won't be able to reconstruct the error trace
		// because the set of initial states is likely to be different.
		// This is only necessary though, if TLCGlobals.enumFraction was < 1 during
		// the generation of inits.
		final Random snapshot = RandomEnumerableValues.reset();
		
		// The vector of fingerprints is now being followed forward from the
		// initial state (which is the last state in the long vector), to the
		// end state.
		//
		// At each fingerprint of the sequence, the equivalent state gets
		// reconstructed. For the initial state it's just the fingerprint, for
		// successor states the predecessor p to the successor state s and the
		// fingerprint that are passed to Tool. Tool generates *all* next states
		// of p and throws away all except the one that has a matching
		// fingerprint.
		int stateNum = 0;
		final int len = records.size() - 1;
		
		final TLCStateInfo[] res = new TLCStateInfo[len];
		if (len > 0) {
			if (sinfo == null) {
				// Recreate initial state from its fingerprint.
				Record record = records.get(len);
				assert record.isInitial();
				sinfo = this.tool.getState(record.fp);
				
				Record prev = records.get(len - 1);
				sinfo.state.workerId = (short) prev.worker;
				sinfo.state.uid = prev.ptr;
			}
			// Recover successor states from its predecessor and its fingerprint.
			res[stateNum++] = sinfo;
			for (int i = len-2; i >= 0; i--) {
				Record record = records.get(i+1);
				long fp = record.fp;
				sinfo = this.tool.getState(fp, sinfo.state);
				if (sinfo == null) {
					/*
					 * The following error message is misleading, because it's triggered when TLC
					 * can't find a non-initial state from its fingerprint when it's generating an
					 * error trace. LL 7 Mar 2012
					 */
					MP.printError(EC.TLC_FAILED_TO_RECOVER_INIT);
					MP.printError(EC.TLC_BUG, "2 " + Long.toString(fp));
					System.exit(1);
				}
				Record prev = records.get(i);
				sinfo.state.workerId = (short) prev.worker;
				sinfo.state.uid = prev.ptr;
				
				res[stateNum++] = sinfo;
			}
		}
		RandomEnumerableValues.set(snapshot);
		return res;
	}
}
