package tlc2.cc;

import java.io.IOException;
import java.util.ArrayList;

import tlc2.cc.CCAction.Type;
import tlc2.tool.Action;
import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValueOutputStream;
import tlc2.value.ValueInputStream;

/**
 * CCAction is a TLA action with round info(round number + round index).
 * 
 */
public class CCAction {
	
	public enum Type{Send, Rcv, BeginGuard, MidGuard, EndGuard, Init}
	static public byte INTVALUE         =  1;
	
	private int roundNumber;
	private int index;
	private Action action;
	private Type type;
	private int level;
	private CCAction[] nexts = null;
	private CCAction next = null;
	
	public CCAction getNext() {
		return next;
	}

	public void setNext(CCAction next) {
		this.next = next;
	}

	public CCAction[] getNexts() {
		return nexts;
	}

	public void setNexts(CCAction[] nexts) {
		this.nexts = nexts;
	}

	public static CCAction Empty = new CCAction(-1,-1,null,Type.Init,Rounds.INIT_LEVEL);

	CCAction(int roundNumber, int index, Action action, Type type, int level) {
		this.roundNumber = roundNumber;
		this.index = index;
		this.action = action;
		this.type = type;
		this.level = level;
	}

	public long fingerPrint(long fp) {
		fp = FP64.Extend(FP64.Extend(fp, INTVALUE), level);
//		fp = FP64.Extend(FP64.Extend(fp, INTVALUE), roundNumber);
//		fp = FP64.Extend(FP64.Extend(fp, INTVALUE), index);
		return fp;
	}

	public Action getAction() {
		return action;
	}
	public Type getType() {
		return type;
	}
	
	public String toString() {

		String str = "[rn = " + roundNumber + ", idx = " + index;
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
	public String toStringH() {

		String str = "";
		String name = action==null ? "NULL" : action.getName() + " " + action.con;
		switch(type) {
		case Init: {
			return "Initial Action";
		}
		case Send:{
			str += "(S)" + name;
			break;
		}
		case Rcv:{
			str += "(R)" + name;
			break;
		}
		default:
		}
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

	public String getLocation() {
		switch(type) {
		case Init:{
			return "< null >";
		}
		case BeginGuard:{
			return "< BeginGuard >";
		}
		case MidGuard:{
			return "< MidGuard >";
		}
		case Send:
		case Rcv:{
			if(action.isNamed()) {
				return "<" + action.getName().toString() + action.con.toString() + " " +  action.pred.getLocation() + ">";
			}else {
				return "< Action Unnamed >";
			}
		}
		case EndGuard: {
			return "< EndGuard >";
		}
		default:{ assert(false);}
		}
		return null;
	}
	
	public void write(IValueOutputStream vos) throws IOException {
		vos.writeInt(roundNumber);
		vos.writeInt(index);
	}
	
	public static CCAction createFrom(ValueInputStream vis) throws IOException {
		int roundNumber = vis.readInt();
		int index = vis.readInt();
		if(roundNumber<0) {
			return CCAction.Empty;
		}
		return CC.getRound(roundNumber).getCCAction(index);
	}
	
	public static void fillNexts(Rounds rounds) {
		CCAction init = Empty;
		
	}

	public String printNexts() {
		String str = "[rn = " + roundNumber + ", idx = " + index;
		switch(type) {
		case Send:{
			int id = action==null ? -1 : action.getId();
			str += ", send = " + id;
			break;
		}
		case Rcv:{
			int id = action==null ? -1 : action.getId();
			str += ", rcv = " + id;
			break;
		}
		}
		str += ", nexts=[";
		for(int i=0;i<nexts.length;i++) {
			str += nexts[i].getAction().getId();
			if(i< nexts.length-1) {
				str += ", ";
			}
		}
		str += "]";
		return str;
	}
	
}
