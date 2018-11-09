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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class NoLoop2Test extends PCalModelCheckerTestCase {

	public NoLoop2Test() {
		super("NoLoop2", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "9"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "11", "9", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "6"));

		assertCoverage("  line 30, col 11 to line 30, col 16 of module NoLoop2: 1\n" +
			"  line 31, col 9 to line 31, col 17 of module NoLoop2: 1\n" +
			"  line 32, col 9 to line 32, col 14 of module NoLoop2: 1\n" +
			"  line 36, col 14 to line 36, col 19 of module NoLoop2: 2\n" +
			"  line 37, col 14 to line 37, col 24 of module NoLoop2: 2\n" +
			"  line 38, col 9 to line 38, col 17 of module NoLoop2: 2\n" +
			"  line 42, col 20 to line 42, col 29 of module NoLoop2: 1\n" +
			"  line 43, col 20 to line 43, col 28 of module NoLoop2: 1\n" +
			"  line 44, col 20 to line 44, col 29 of module NoLoop2: 1\n" +
			"  line 45, col 20 to line 45, col 28 of module NoLoop2: 1\n" +
			"  line 46, col 9 to line 46, col 14 of module NoLoop2: 2\n" +
			"  line 49, col 9 to line 49, col 18 of module NoLoop2: 1\n" +
			"  line 50, col 9 to line 50, col 17 of module NoLoop2: 1\n" +
			"  line 51, col 9 to line 51, col 14 of module NoLoop2: 1\n" +
			"  line 55, col 9 to line 55, col 20 of module NoLoop2: 2\n" +
			"  line 56, col 19 to line 56, col 28 of module NoLoop2: 0\n" +
			"  line 60, col 41 to line 60, col 44 of module NoLoop2: 0");
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup NoLoop2.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file NoLoop2.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\TLC.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TLC
Semantic processing of module NoLoop2
Starting... (2012-08-10 17:38:22)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated.
7  TRUE
7  TRUE
10  TRUE
10  TRUE
Checking temporal properties for the complete state space...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 9.8E-19
  based on the actual fingerprints:  val = 1.6E-17
11 states generated, 9 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 6.
Finished. (2012-08-10 17:38:22)
*/