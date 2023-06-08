package tlc2.cc;

import java.util.ArrayList;

import tlc2.tool.Action;
import tlc2.tool.TLCState;

public class Rounds {
	
	private ArrayList<Round> rounds = new ArrayList<>();
	public static final int INIT_LEVEL = TLCState.INIT_LEVEL;
	private static int CCActionCount = INIT_LEVEL;
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
