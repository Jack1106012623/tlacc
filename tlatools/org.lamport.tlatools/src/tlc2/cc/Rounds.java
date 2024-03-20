package tlc2.cc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tla2sany.semantic.OpDefNode;
import tlc2.cc.CCAction.Type;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.util.Context;

public class Rounds {
	
	private ArrayList<Round> rounds = new ArrayList<>();
	public static final int INIT_LEVEL = TLCState.INIT_LEVEL;
	private static int CCActionCount = INIT_LEVEL;

	public static String Action_Id = "\\w+";
  public static String Action_Args = String.format("\\([a-zA-Z0-9_*,]+\\)");
  public static String Action = String.format("%s(?:%s)?", Action_Id, Action_Args);
  public static String Actions = String.format("%s(?:\\+%s)*", Action, Action);
  public static String RE_Round = String.format("\\[(%s),(%s)\\]",Actions, Actions);
  public static String RE_Action = String.format("(%s)(%s)?", Action_Id, Action_Args);
	/**
	 * @param i : Starting with 0
	 * @return Round i
	 */
	public Round getRound(int i) {
		if(i>= rounds.size()) {
			return null;
		}
		return rounds.get(i);
	}
	
	public int size() {
		return rounds.size();
	}
	
	public int firstRoundId() {
		return 0;
	}
	public boolean isFirstRound(int id) {
		return id == 0;
	}
	public boolean isLastRound(int id) {
		return id == rounds.size()-1;
	}
	
	
	private List<Action> getValidAction(String actionName, String actionArgs){
		// actionArgs: (1,*), null
		String[] args = null;
		if(actionArgs != null) {
			args = actionArgs.substring(1, actionArgs.length()-1).split(",");
		}
		
		if(actionName.equals("NULL")) {
			return null;
		}
		
		List<Action> actions = CC.actionMap.get(actionName);
		if(actions==null) {
			CC.printError("No such action: " + actionName);
			System.exit(1);
		}
		
		List<Action> ret=null;
		for(Action action:actions) {
			OpDefNode opDef = action.getOpDef();
			if(opDef == null) {
				CC.printError("CC currently do not support such action: " + actionName);
				System.exit(1);
			}
			int arity = opDef.getArity();
			if(arity == -1) {
				CC.printError("CC currently do not support variable number of args: " + actionName);
				System.exit(1);
			}
			int args_length = args == null ? 0 : args.length;
			if(arity == args_length) {
				Context ctx = action.con;
				boolean valid = true;
				for(int i=args_length-1;i>=0;i--,ctx = ctx.next()) {
					if(!args[i].equals("*") && !ctx.getValue().toString().equals(args[i])) {
						valid = false;
						break;
					}
				}
				if(valid) {
					if(ret == null) {
						ret = new ArrayList<Action>();
					}
					ret.add(action);
				}
			}
		}
		if(ret==null) {
			CC.printError("No action with args: " + actionArgs);
			System.exit(1);
		}
		return ret;
	}

	public void addRound(String line) {
		Pattern round_pattern = Pattern.compile(RE_Round);
		Matcher round_matcher = round_pattern.matcher(line);
		if (round_matcher.matches()) {
			String[] sends = round_matcher.group(1).split("\\+");
			String[] rcvs = round_matcher.group(2).split("\\+");
			Pattern action_pattern = Pattern.compile(RE_Action);
			
			List<Action> sendActions = new ArrayList<>(1), rcvActions = new ArrayList<>(1);
			for (String send : sends) {
				if(send.equals("NULL")) {
					sendActions = null;
					break;
				}
				Matcher action_matcher = action_pattern.matcher(send);
				if (action_matcher.matches()) {
					String aname = action_matcher.group(1);
					String aargs = action_matcher.group(2);
					sendActions.addAll(getValidAction(aname, aargs));
				} else {
					CC.printError("Syntax Error: " + line);
				}
			}
			for (String rcv : rcvs) {
				if(rcv.equals("NULL")) {
					rcvActions = null;
					break;
				}
				Matcher action_matcher = action_pattern.matcher(rcv);
				if (action_matcher.matches()) {
					String aname = action_matcher.group(1);
					String aargs = action_matcher.group(2);
					rcvActions.addAll(getValidAction(aname, aargs));
				}else {
					CC.printError("Syntax Error: " + line);
				}
			}
			String RoundName = "";
			addRound(RoundName, sendActions, rcvActions);
		} else {
			CC.printError("Syntax Error: " + line);
		}
	}
	public void addRound(String name, List<Action> sends, List<Action> rcvs) {
		Action[] sendActions=null, rcvActions=null;

		if(sends != null){
			sendActions = new Action[sends.size()];
			for(int i=0; i< sends.size();i++) {
				sendActions[i] = sends.get(i);
			}
		}
		
		if(rcvs != null) {
			rcvActions = new Action[rcvs.size()];
			for(int i=0; i< rcvs.size();i++) {
				rcvActions[i] = rcvs.get(i);
			}
		}
		if(rounds.size()==0 && sends==null) {
			System.out.println("First Action should be Send");
			System.exit(-1);
		}
		rounds.add(new Round(name, rounds.size(), sendActions, rcvActions));
		
	}
	public void addRound(String name, int[] sendIds, int[] rcvIds) {
		Action[] sendActions=null, rcvActions=null;

		if(sendIds != null){
			sendActions = new Action[sendIds.length];
			for(int i=0; i< sendIds.length;i++) {
				int id = sendIds[i];
				sendActions[i] = CC.id2Action.get(id);
			}
		}
		
		if(rcvIds != null) {
			rcvActions = new Action[rcvIds.length];
			for(int i=0; i< rcvIds.length;i++) {
				int id = rcvIds[i];
				rcvActions[i] = CC.id2Action.get(id);
			}
		}
		rounds.add(new Round(name, rounds.size(), sendActions, rcvActions));
		
	}
	public void print() {
		System.out.println("Printing rounds...");
		for(int i=0;i<rounds.size();i++) {
			rounds.get(i).printH();
		}
	}
	public CCAction getFirstAction() {
		return rounds.get(0).getCCAction(0);
	}
	public boolean isLastAction(CCAction action) {
		int rn = action.getRoundNumber();
		int idx = action.getIndex();
		return isLastRound(rn) && rounds.get(rn).isLastIndex(idx);
	}
	
	public CCAction getNext(CCAction action) {
		
		if(action.getType() == Type.Init) {
			return this.getFirstAction();
		}
		
		int rn = action.getRoundNumber();
		int idx = action.getIndex();
		if(getRound(rn).isLastIndex(idx)) {
			// last action
			if(isLastRound(rn)) {
				return null;
			}
			// next round's first action
			return getRound(rn+1).getFirstAction();
		} else {
			// next action
			return getRound(rn).getNext(action);
		}
	}
	public static int newLevel() {
		return ++CCActionCount;
	}

	public CCAction getNextSend(int preRoundId) {
		for(int i=preRoundId+1;i<rounds.size();i++) {
			Round r = getRound(i);
			if(r.hasSend()) {
				return r.getFirstAction();
			}
		}
		return null;
	}

	public void printNexts() {
		System.out.println("Printing next actions...");
		for(int i=0;i<rounds.size();i++) {
			rounds.get(i).printNexts();
		}
	}

}
