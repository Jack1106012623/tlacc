package tlc2.cc;

import tlc2.cc.CCAction.Type;
import tlc2.tool.Action;

/**
 * CCIterator is used to go through CC rounds to determine the next permitted actions.
 * CCIterator lies between two actions.
 */
public class CCAction {
	public enum Type{Send, Rcv, BeginGuard, MidGuard, EndGuard, Init}
	
	private int roundNumber;
	private int index;
	private Action action;
	private Type type;
	private int level;
	
	CCAction(int roundNumber, int index, Action action, Type type, int level) {
		this.roundNumber = roundNumber;
		this.index = index;
		this.action = action;
		this.type = type;
		this.level = level;
	}

	public long fingerPrint() {
		return roundNumber * 137 + index;
	}

	public Action getAction() {
		return action;
	}
	public Type getType() {
		return type;
	}
	
	public String toString() {

		String str = "[round = " + roundNumber + ", level = " + level;
		
		switch(type) {
		case Init: {
			return "Initial Action";
		}
		case BeginGuard: {
			str += ", BeginGuard";
			break;
		}
		case Send:{
			int id = action==null ? -1 : action.getId();
			str += ", send = " + id;
			break;
		}
		case MidGuard:{
			str += ", MidGuard";
			break;
		}
		case Rcv:{
			int id = action==null ? -1 : action.getId();
			str += ", rcv = " + id;
			break;
		}
		case EndGuard: {
			str += ", EndGuard";
			break;
		}
		
		default:
		}
		str += "]";
		return str;
	}
	
	public int getRoundNumber() {
		return roundNumber;
	}

	public int getIndex() {
		return index;
	}

	public int getLevel() {
		return level;
	}

	public void setLevel(int level) {
		this.level = level;
	}
}
