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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.OpDefNode;
import tla2sany.st.Location;
import tla2sany.st.TreeNode;
import tlc2.tool.Action;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.RecordValue;

public class TLCSuccessorsStackFrame extends TLCStateStackFrame {

	private transient final INextStateFunctor fun;

	public TLCSuccessorsStackFrame(TLCStackFrame parent, OpDefNode node, Context ctxt, Tool tool, TLCState s, Action a,
			INextStateFunctor fun) {
		super(parent, node, ctxt, tool, s);
		this.fun = fun;
		//TODO Append action name, too? => node.getName().toString()
		// Overwrite setName from parent that uses HumanReadableImage, which -for an
		// OpDefNode- is not the location.
		setName(node.toString());
	}
	
	public int getSuccessorId() {
		// +4 because TLCStateStackFrame and TLCStackFrame already use up ctxtId+1,
		// ctxtId+2, and ctxtId+3.
		return this.ctxtId + 4;
	}
	
	@Override
	public Variable[] getVariables(int vr) {
		if (vr == getSuccessorId()) {
			return tool.eval(() -> {
				final Iterator<TLCState> iterator = fun.getStates().iterator();
				final Variable[] vars = new Variable[fun.getStates().size()];
				for (int i = 0; i < vars.length; i++) {
					RecordValue r = new RecordValue(iterator.next());
					vars[i] = getStateAsVariable(r, "t" + (i+1));
				}
				return vars;
				// If the label tN: left of the state in the variable view of the debugger turns
				// out useless, the map/collect below is equivalent to the for loop above.
//				return fun.getStates().stream().map(s -> getStateAsVariable(new RecordValue(s), ""))
//						.collect(Collectors.toList()).toArray(Variable[]::new);
			});
		}
		return super.getVariables(vr);
	}
	
	@Override
	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		scopes.addAll(Arrays.asList(super.getScopes()));
		
		final Scope scope = new Scope();
		scope.setName("Successors");
		scope.setVariablesReference(getSuccessorId());
		// Move "Successors" above "Trace".  This is brittle!
		scopes.add(scopes.size() - 1, scope);
		
		return scopes.toArray(new Scope[scopes.size()]);
	}
	
	@Override
	public boolean matches(final TLCSourceBreakpoint bp) {
		final OpDefNode odn = (OpDefNode) node;
		// TreeNode.one()[0] is the LHS of the definition => A user activates is by
		// setting an "in-line" breakpoint into the LHS of the def.
		if (odn.getTreeNode() != null && odn.getTreeNode().one().length > 0) {
			final TreeNode[] one = odn.getTreeNode().one();
			final Location location = one[0].getLocation();
			final int hits = bp.getHits();
			return bp.getLine() == location.beginLine() && location.beginColumn() <= bp.getColumnAsInt()
					&& bp.getColumnAsInt() <= location.endColumn() && fun.getStates().size() >= hits;
		}
		return false;
	}
}
