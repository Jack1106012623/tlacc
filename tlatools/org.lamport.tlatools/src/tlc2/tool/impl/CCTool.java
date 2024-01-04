package tlc2.tool.impl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tlc2.cc.CC;
import tlc2.cc.CCAction;
import tlc2.cc.CCAction.Type;
import tlc2.output.EC;
import tlc2.cc.CCState;
import tlc2.cc.TLCStateMutCC;
import tlc2.tool.Action;
import tlc2.tool.EvalException;
import tlc2.tool.IActionItemList;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.Worker;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.util.ExpectInlined;
import tlc2.util.IdThread;
import tlc2.value.IValue;
import tlc2.value.impl.SetDiffValue;
import tlc2.value.impl.Value;
import util.FilenameToStream;
import util.Assert.TLCRuntimeException;

/**
 * CCTool is for communication closure.
 */
public final class CCTool extends Tool {
	public CCTool(String mainFile, String configFile, String roundsFile , FilenameToStream resolver, Map<String, Object> params) {
		super(mainFile, configFile, resolver, params);
		
		CC.init(this, roundsFile);
	}

	@Override
  public boolean getNextStates(final INextStateFunctor functor, final TLCState state) {
//		System.out.println("XXX get Next states, cur state = " + state);
//		System.out.println("XXX get Next states");
		CCState ccstate = ((TLCStateMutCC)state).getCCState();
	  ArrayList<CCAction> list = CC.getNextActions(ccstate);
	  
	  if(list.size()==1 && list.get(0).getType() == Type.Send) {
	  	list = CC.getNextSendsAndMid(ccstate);
	  	for (int i = 0; i < list.size(); i++) {
  			this.getNextStates(functor, state, list.get(i));
  			if(ccstate.isActionExecuted()) {
	  			break;
	  		}
	  	}
	  	return false;
	  }
	  for (int i = 0; i < list.size(); i++) {
	  	this.getNextStates(functor, state, list.get(i));
		}
		return false;
		
  }
	// if send cannot execute, return true
	public boolean getNextStates(final INextStateFunctor functor, TLCState state, CCAction next) {
		Action action = next.getAction();
	
		
		switch(next.getType()) {
		case Init:{
			System.out.println("Should not get Init");
			assert(false);
			break;
		}
		case BeginGuard:{
			if(next.getLevel()<=2) {
//				System.out.println("???");
			}
			IValue newMsgs = CC.getBeginRoundMsgs(state);
			TLCState s1 = state.copy();
			((TLCStateMutCC)s1).setCCState(new CCState(next));
			s1.bind(CC.getMsgs(), newMsgs);
			functor.addElement(state,action,s1);
			break;
		}
		case MidGuard:{
			TLCState s1 = state.copy();
			CCState ccs1 = ((TLCStateMutCC)s1).getCCState();
			IValue msgs = state.lookup(CC.getMsgs());
			ccs1.setMsgs1(msgs);
			ccs1.setPre(next);
			ccs1.setActionExecuted(false);
			functor.addElement(state,action,s1);
			break;
		}
		case Send:
		case Rcv:{
			TLCState s1 = TLCState.Empty.createEmpty().setPredecessor(state).setAction(action);
			CCState ccs1 = ((TLCStateMutCC)state).getCCState().copy();
			ccs1.setPre(next);
			ccs1.setActionExecuted(false);
			((TLCStateMutCC)s1).setCCState(ccs1);
			this.getNextStates(action, action.pred, ActionItemList.Empty, action.con, state,
					s1, functor, action.cm);
			break;
		}
		case EndGuard: {
			TLCState s1 = state.copy();
			CCState ccs1 = ((TLCStateMutCC)s1).getCCState();
			IValue msgs = state.lookup(CC.getMsgs());
			ccs1.setMsgs2(msgs);
			ccs1.setPre(next);
			ccs1.setActionExecuted(false);
			functor.addElement(state,action,s1);
			break;
		}
		default:{ assert(false);}
		}
		return false;
		
	}
	
	
	// The methods below are supposed to be inlined during execution for performance
	// reasons, collapsing this class effectively into Tool. Later and in case of a
	// violation, the CCTool instance will be exchanged for the CallStackTool
	// instance that properly records error for the purpose of error reporting.
	@ExpectInlined
	@Override
	protected final TLCState getNextStates(final Action action, final SemanticNode pred, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		return getNextStatesImpl(action, pred, acts, c, s0, s1, nss, cm);
	}

	@ExpectInlined
	@Override
	protected final TLCState getNextStatesAppl(final Action action, final OpApplNode pred, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		return getNextStatesApplImpl(action, pred, acts, c, s0, s1, nss, cm);
	}

	@ExpectInlined
	@Override
	protected final TLCState processUnchanged(final Action action, final SemanticNode expr, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		return processUnchangedImpl(action, expr, acts, c, s0, s1, nss, cm);
	}

	@ExpectInlined
	@Override
	public final Value eval(final SemanticNode expr, final Context c, final TLCState s0, final TLCState s1,
			final int control, final CostModel cm) {
		return evalImpl(expr, c, s0, s1, control, cm);
	}

	@ExpectInlined
	@Override
	protected final Value evalAppl(final OpApplNode expr, final Context c, final TLCState s0, final TLCState s1,
			final int control, final CostModel cm) {
		return evalApplImpl(expr, c, s0, s1, control, cm);
	}

	@ExpectInlined
	@Override
	protected final Value setSource(final SemanticNode expr, final Value value) {
		return value;
	}

	@ExpectInlined
	@Override
	public final TLCState enabled(final SemanticNode pred, final IActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		return enabledImpl(pred, (ActionItemList) acts, c, s0, s1, cm); // TODO This cast sucks performance-wise.
	}

	@ExpectInlined
	@Override
	protected final TLCState enabledAppl(final OpApplNode pred, final ActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		return enabledApplImpl(pred, acts, c, s0, s1, cm);
	}

	@ExpectInlined
	@Override
	protected final TLCState enabledUnchanged(final SemanticNode expr, final ActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		return enabledUnchangedImpl(expr, acts, c, s0, s1, cm);
	}
	
  public final StateVec getNextStates(CCAction next, TLCState state) {
		StateVec nss = new StateVec(0);
		this.getNextStates(nss, state, next);
		
		return nss;
  }
  
	
	@Override
  public final TLCStateInfo getState(long fp, TLCState s) {
	  IdThread.setCurrentState(s);
	  
	  StateVec nextStates = new StateVec(0);
	  CCState ccstate = ((TLCStateMutCC)s).getCCState();
	  ArrayList<CCAction> list = CC.getNextActions(ccstate);
	  if(list.size()==1 && list.get(0).getType() == Type.Send) {
	  	list = CC.getNextSendsAndMid(ccstate);
	  }
	  
  	for (int i = 0; i < list.size(); i++) {
  		CCAction ccaction = list.get(i);
  		nextStates = this.getNextStates(ccaction, s);
			for (int j = 0; j < nextStates.size(); j++) {
        TLCState state = nextStates.elementAt(j);
        long nfp = state.fingerPrint();
        if (fp == nfp) {
        	state.setPredecessor(s);
        	assert !state.isInitial();
        	return new TLCStateInfo(state, ccaction);
        }
      }
		}
	  
		return null;
  }
	@Override
  public final TLCStateInfo getState(TLCState s1, TLCState s) {
	  IdThread.setCurrentState(s);
	  StateVec nextStates = new StateVec(0);
	  CCState ccstate = ((TLCStateMutCC)s).getCCState();
	  ArrayList<CCAction> list = CC.getNextActions(ccstate);
	  if(list.size()==1 && list.get(0).getType() == Type.Send) {
	  	list = CC.getNextSendsAndMid(ccstate);
	  }
  	for (int i = 0; i < list.size(); i++) {
  		CCAction ccaction = list.get(i);
  		nextStates = this.getNextStates(ccaction, s);
			for (int j = 0; j < nextStates.size(); j++) {
        TLCState state = nextStates.elementAt(j);
        try {
        	if (s1.equals(state)) {
        		state.setPredecessor(s);
        		assert !state.isInitial();
        		return new TLCStateInfo(state, ccaction);
        	}
        } catch (TLCRuntimeException e) {
        	continue;
        }
        
      }
		}
    return null;
  }
}
