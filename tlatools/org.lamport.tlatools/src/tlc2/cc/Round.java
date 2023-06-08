package tlc2.cc;

import java.util.ArrayList;

import tlc2.cc.CCAction.Type;
import tlc2.tool.Action;

/**
 * A Round is a CCIterator list including some TLA actions and three guard.
 * BeginGuard is used to calculate the message channel at the beginning of the round.
 * MidGuard is used to store messages which belong to this round.
 * EndGuard is used to store messages which include this and next round's message.
 */

public class Round {
	
	private String name;
	private int id;
	
	/**
	 * iters store all CCIterators of a round
	 */
	private ArrayList<CCAction> iters = new ArrayList<>();
	
	
	
	public Round(String name, int id, Action[] sends, Action[] rcvs) {
		this.name = name;
		this.id = id;
		
		iters.add(new CCAction(id, iters.size(), null, Type.BeginGuard, Rounds.newLevel()));
		
		if(sends != null) {
			for(int i=0;i<sends.length;i++) {
				iters.add(new CCAction(id, iters.size(), sends[i], Type.Send, Rounds.newLevel()));
			}
		}

		iters.add(new CCAction(id, iters.size(), null, Type.MidGuard, Rounds.newLevel()));
		if(rcvs != null) {
			for(int i=0;i<rcvs.length;i++) {
				iters.add(new CCAction(id, iters.size(), rcvs[i], Type.Rcv, Rounds.newLevel()));
			}
		}
		iters.add(new CCAction(id, iters.size(), null, Type.EndGuard, Rounds.newLevel()));
	}
	
	
	public boolean end(int index) {
		return index >= iters.size();
	}
	
	public CCAction getEndGuard() {
		return iters.get(iters.size()-1);
	}
	public CCAction getBeginGuard() {
		return iters.get(0);
	}
	public CCAction getCCAction(int i) {
		return iters.get(i);
	}
	
	public void print() {
		String str = "round : " + id + ": [";
		for(int i=0;i<iters.size();i++) {
			str += iters.get(i).toString() + ", ";
		}
		str += "]";
		System.out.println(str);
	}
}





