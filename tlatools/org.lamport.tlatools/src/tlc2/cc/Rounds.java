package tlc2.cc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tlc2.tool.Action;
import tlc2.tool.TLCState;

public class Rounds {
	
	private ArrayList<Round> rounds = new ArrayList<>();
	public static final int INIT_LEVEL = TLCState.INIT_LEVEL;
	private static int CCActionCount = INIT_LEVEL;

	public static String RE_Action = "(\\w+)(\\(.*\\))?";
	public static String RE_Round = "\\["+ RE_Action + "," + RE_Action + "\\]";
			
	/**
	 * @param i : Starting with 0
	 * @return Round i
	 */
	public Round getRound(int i) {
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
	public void addRound(String line) {
		Pattern pattern = Pattern.compile(RE_Round);
        Matcher matcher = pattern.matcher(line);
        String SendName = null, SendArgs=null, RcvName=null, RcvArgs=null;
        if (matcher.find()) {
            int group = 1;
            SendName = matcher.group(group++);
            if(SendName!="NULL"){
                SendArgs = matcher.group(group++);
            }
            RcvName = matcher.group(group++);
            if(RcvName!="NULL"){
                RcvArgs = matcher.group(group);
            }
        }
		List<Action> sendActions=null, rcvActions=null;
		if(SendName!="NULL") {
			sendActions = CC.actionMap.get(SendName);
		}
		if(RcvName!="NULL") {
			rcvActions = CC.actionMap.get(RcvName);
		}
		String RoundName = "";
		addRound(RoundName, sendActions, rcvActions);
		
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
			rounds.get(i).print();
		}
	}
	public CCAction getNext(CCAction action) {
		
		assert(action != null);
		switch(action.getType()) {
		case Init:{
			return rounds.get(0).getBeginGuard();
		}
		case BeginGuard:
		case Send:
		case MidGuard:
		case Rcv:{
			return rounds.get(action.getRoundNumber()).getCCAction(action.getIndex()+1);
		}
		case EndGuard: {
			if(isLastRound(action.getRoundNumber())) {
				return null;
			}
			return rounds.get(action.getRoundNumber()+1).getBeginGuard();
		}
		default:{ assert(false);return null;}
		}
	}
	public static int newLevel() {
		return ++CCActionCount;
	}
}
