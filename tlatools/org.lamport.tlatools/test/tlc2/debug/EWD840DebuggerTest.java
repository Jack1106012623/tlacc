/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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
package tlc2.debug;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tla2sany.semantic.OpDeclNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.IntValue;

public class EWD840DebuggerTest extends TLCDebuggerTestCase {

	// MC02 is the spec that extends EWD840 and assigns values to constants for TLC.
	private static final String RM = "EWD840";
	private static final String MDL = "MC02";

	public EWD840DebuggerTest() {
		super(MDL, RM, EC.ExitStatus.SUCCESS, createBreakpointArgument(RM,23));
	}

	@Test
	public void testSpec() throws Exception {
		StackFrame[] stackFrames = debugger.stackTrace();
		assertEquals(1, stackFrames.length);

		assertTLCFrame(stackFrames[0], 5, 5, RM);
		// prefix depends on where the tests execute.
		assertTrue(stackFrames[0].getSource().getPath().endsWith("test-model/EWD840/EWD840.tla"));
		stackFrames = debugger.stepIn();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 5, 5, RM);
		assertTLCFrame(stackFrames[0], 5, 5, RM);

		// The order of vars is expected to be deterministic across tests (local,
		// because TLCState.Empty is null during ctor-time).
		final Tool tool = (Tool) TLCGlobals.mainChecker.tool;
		final OpDeclNode[] vars = tool.getSpecProcessor().getVariablesNodes();

		// The spec has 16 initial states over which we will continue each time checking
		// the stack frames:
		for (int i = 0; i < 16; i++) { //64
			stackFrames = debugger.continue_();

			assertEquals(5, stackFrames.length);
			assertTLCStateFrame(stackFrames[4], 20, 23, RM, vars);
			assertTLCStateFrame(stackFrames[3], 20, 20, RM, vars);
			assertTLCStateFrame(stackFrames[2], 21, 21, RM, vars[0], vars[2], vars[3]);
			assertTLCStateFrame(stackFrames[1], 22, 22, RM, vars[0], vars[2]);
			assertTLCStateFrame(stackFrames[0], 23, 23, RM, vars[2]);

			// TODO: The semantics of continue are broken because we hit the same line
			// breakpoint again, which is not what one would "continue" to do.
			stackFrames = debugger.continue_();

			assertEquals(6, stackFrames.length);
			assertTLCStateFrame(stackFrames[5], 20, 23, RM, vars);
			assertTLCStateFrame(stackFrames[4], 20, 20, RM, vars);
			assertTLCStateFrame(stackFrames[3], 21, 21, RM, vars[0], vars[2], vars[3]);
			assertTLCStateFrame(stackFrames[2], 22, 22, RM, vars[0], vars[2]);
			assertTLCStateFrame(stackFrames[1], 23, 23, RM, vars[2]);
			assertTLCStateFrame(stackFrames[0], 23, 23, RM);
		}

		// Debug the InitiateProbe action of the next-state relation.
		debugger.setBreakpoints(RM, 26);
		stackFrames = debugger.continue_();

		// First frame captures the complete action.
		assertEquals(1, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 26, 31, RM, vars);

		// Second frame captures the first line.
		stackFrames = debugger.stepIn();
		assertEquals(2, stackFrames.length);
		assertTLCActionFrame(stackFrames[1], 26, 31, RM, vars);
		assertTLCActionFrame(stackFrames[0], 26, 26, RM, vars);

		// Third frame.
		stackFrames = debugger.stepIn();
		assertEquals(3, stackFrames.length);
		assertTLCActionFrame(stackFrames[2], 26, 31, RM, vars);
		assertTLCActionFrame(stackFrames[1], 26, 26, RM, vars);
		assertTLCActionFrame(stackFrames[0], 26, 26, RM, vars);

		// Fourth frame.
		stackFrames = debugger.stepIn();
		assertEquals(3, stackFrames.length);
		assertTLCActionFrame(stackFrames[2], 26, 31, RM, vars);
		assertTLCActionFrame(stackFrames[1], 26, 26, RM, vars);
		assertTLCActionFrame(stackFrames[0], 27, 27, RM, vars);

		// Debug the SendMsg action of the next-state relation.
		debugger.setBreakpoints(RM, 46);
		stackFrames = debugger.continue_();
		assertEquals(4, stackFrames.length);
		Context context = Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne);
		/*
		  /\ active[i]
		  /\ \E j \in Nodes \ {i} :
		        /\ active' = [active EXCEPT ![j] = TRUE]
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		  /\ UNCHANGED <<tpos, tcolor>>
		 */
		assertTLCActionFrame(stackFrames[3], 44, 48, RM, context, vars);
		/*
		  /\ active[i]
		 */
		assertTLCActionFrame(stackFrames[2], 44, 44, RM, context, vars);
		/*
		  /\ \E j \in Nodes \ {i} :
		        /\ active' = [active EXCEPT ![j] = TRUE]
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		 */
		assertTLCActionFrame(stackFrames[1], 45, 47, RM, context, vars);
		/*
		        /\ active' = [active EXCEPT ![j] = TRUE]
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		 */
		context = context.cons(null, IntValue.ValZero);
		assertTLCActionFrame(stackFrames[0], 46, 47, RM, context, vars);

		/*
        		/\ active' = [active EXCEPT ![j] = TRUE]
		 */
		stackFrames = debugger.stepIn();
		assertEquals(5, stackFrames.length);
		context = Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne);
		assertTLCActionFrame(stackFrames[4], 44, 48, RM, context, vars);
		assertTLCActionFrame(stackFrames[3], 44, 44, RM, context, vars);
		assertTLCActionFrame(stackFrames[2], 45, 47, RM, context, vars);
		context = context.cons(null, IntValue.ValZero);
		assertTLCActionFrame(stackFrames[1], 46, 47, RM, context, vars);
		assertTLCActionFrame(stackFrames[0], 46, 46, RM, context, vars);

		/*
				[active EXCEPT ![j] = TRUE]
				The breakpoint on this line (46) means that step in/out/over
				takes precedence.
		 */
		stackFrames = debugger.next();
		assertEquals(6, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 46, 46, RM, context, vars);
		/*
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		 */
		stackFrames = debugger.next();
		assertEquals(6, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 47, 47, RM, context, vars[0], vars[2], vars[3]);

		/*
  				/\ UNCHANGED <<tpos, tcolor>>
		 */
		stackFrames = debugger.stepIn(4);
		assertEquals(7, stackFrames.length);
		context = Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne);
		assertTLCActionFrame(stackFrames[0], 48, 48, RM, context, vars[0], vars[2]);
		
		// 8888888888888888888 State Constraint 8888888888888888888 //
		debugger.setBreakpoints(MDL, 16);
		stackFrames = debugger.continue_();
		stackFrames = debugger.stepIn(9);
		assertEquals(11, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 16, 16, MDL, Context.Empty.cons(null, IntValue.ValOne));
		Variable[] contextVariables = ((TLCStateStackFrame) stackFrames[0]).getVariables();
		assertNotNull(contextVariables);
		assertEquals(1, contextVariables.length);
		Variable variable = contextVariables[0];
		assertEquals("node", variable.getName());
		assertEquals("IntValue", variable.getType());
		assertEquals("1", variable.getValue());
		
		// 8888888888888888888 Action Constraint 8888888888888888888 //
		debugger.setBreakpoints(MDL, 19);
		stackFrames = debugger.continue_();
		assertEquals(9, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 19, 21, MDL);
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
