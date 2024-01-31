package tlc2.cc;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

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
	private ArrayList<CCAction> actions = new ArrayList<>();
	boolean hasSend = false;
	boolean hasRcv = false;
	private int lastSendIndex = -1;
	
	public Round(String name, int id, Action[] sends, Action[] rcvs) {
		this.name = name;
		this.id = id;
		
		if(sends != null) {
			hasSend = true;
			for(int i=0;i<sends.length;i++) {
				actions.add(new CCAction(id, actions.size(), sends[i], Type.Send, Rounds.newLevel()));
			}
			lastSendIndex = sends.length - 1;
		}

		if(rcvs != null) {
			hasRcv = true;
			for(int i=0;i<rcvs.length;i++) {
				actions.add(new CCAction(id, actions.size(), rcvs[i], Type.Rcv, Rounds.newLevel()));
			}
		}
	}
	
	
	public boolean isLastIndex(int index) {
		return index == actions.size()-1;
	}
	public int size() {
		return actions.size();
	}
	
	public CCAction getEndGuard() {
		return actions.get(actions.size()-1);
	}
	public CCAction getBeginGuard() {
		return actions.get(0);
	}
	public CCAction getCCAction(int index) {
		return actions.get(index);
	}
	public List<CCAction> getNexts(CCAction action) {
		int index = action.getIndex();
		return actions.subList(index+1, actions.size());
	}
	public List<CCAction> getAllActions(int index) {
		return getNexts(-1);
	}
	public void print() {
		String str = "round " + id + ": [";
		for(int i=0;i<actions.size();i++) {
			str += actions.get(i).toString() + ", ";
		}
		str += "]";
		System.out.println(str);
	}


	public boolean isLastSend(CCAction pre) {
		int idx = pre.getIndex();
		return idx == lastSendIndex;
	}


	public CCAction getNext(CCAction pre) {
		int idx = pre.getIndex();
		if(idx+1 == actions.size()) {
			return null;
		}else {
			return actions.get(idx+1);
		}
	}


	public boolean hasRcv() {
		return hasRcv;
	}


	public boolean hasSend() {
		return hasSend;
	}


	public CCAction getFirstAction() {
		return actions.get(0);
	}


	public List<CCAction> getAllRcvs() {
		return getNexts(lastSendIndex);
	}


	private List<CCAction> getNexts(int index) {
		return actions.subList(index+1, actions.size());
	}


	public void printNexts() {
		String str = "round " + id + ": [";
		for(int i=0;i<actions.size();i++) {
			str += actions.get(i).printNexts();
			if(i<actions.size()-1) {
				str += ", ";
			}
		}
		str += "]";
		System.out.println(str);
		
	}
}





