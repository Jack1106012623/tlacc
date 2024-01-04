package tlc2.cc;

import java.io.IOException;

import tlc2.cc.CCAction.Type;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.ValueInputStream;
import tlc2.value.Values;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueExcept;
import util.WrongInvocationException;


/**
 * CCState stores round info and message channel's temporal state.
 * 
 */
public class CCState extends Value implements Cloneable {
	/**
	 * Store round info using a CCAction.
	 */
	private CCAction pre = null;
	/**
	 * msgs1 stores current round's messages and msgs2 stores next round's initial messages(For Rcv_U_Send).
	 */
	private IValue msgs1 = null;
	private IValue msgs2 = null;
	
	/**
	 * To handle sends cannot perform.
	 */
	private boolean actionExecuted = false;
	
	
	public boolean isActionExecuted() {
		return actionExecuted;
	}

	public void setActionExecuted(boolean actionExecuted) {
		this.actionExecuted = actionExecuted;
	}


	public static CCState Empty = new CCState(CCAction.Empty);
	
	public CCState(CCAction pre) {
		this.pre = pre;
	}
	
	public CCState(CCAction pre, IValue msgs1, IValue msgs2) {
		this.pre = pre;
		this.msgs1 = msgs1;
		this.msgs2 = msgs2;
	}

	public CCAction getPre() {
		return pre;
	}

	public void setPre(CCAction pre) {
		this.pre = pre;
	}

	public IValue getMsgs1() {
		return msgs1;
	}

	public void setMsgs1(IValue msgs1) {
		this.msgs1 = msgs1;
	}

	public IValue getMsgs2() {
		return msgs2;
	}

	public void setMsgs2(IValue msgs2) {
		this.msgs2 = msgs2;
	}

	
	public static CCState createEmpty() {
		return Empty.copy();
	}
	
	public CCState copy() {
		return new CCState(pre, msgs1, msgs2);
	}
	public CCState deepCopy() {
		IValue msgs1_copy = msgs1 == null ? null : msgs1.deepCopy();
		IValue msgs2_copy = msgs2 == null ? null : msgs2.deepCopy();
		return new CCState(pre, msgs1_copy, msgs2_copy);
	}
	
	
	public int getLevel() {
		return pre.getLevel();
	}
	
	// Only need to hash ccIter.
	public long fingerPrint(long fp) {
		return this.pre.fingerPrint(fp);
	}

	@Override
	public int compareTo(Object val) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean isNormalized() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinite() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean isDefined() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
		// TODO Auto-generated method stub
		try {
			String str_pre = "CCIterator: " + pre.toString();
			String str_msg1 = msgs1 == null ? ", msgs1 = null" : ", msgs1 = " + msgs1.size();
			String str_msg2 = msgs2 == null ? ", msgs2 = null" : ", msgs2 = " + msgs2.size();
			sb.append(str_pre).append(str_msg1).append(str_msg2);
			return sb;
		} catch (RuntimeException | OutOfMemoryError e) {
			throw e;
		}
		
	}

	@Override
	public byte getKind() {
		return CCVALUE;
	}

	@Override
	public boolean member(Value elem) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Value takeExcept(ValueExcept ex) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Value takeExcept(ValueExcept[] exs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean assignable(Value val) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Value normalize() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
  public void write(IValueOutputStream vos) throws IOException {
		vos.writeByte(CCVALUE);
		pre.write(vos);
		if(msgs1 == null) {
			vos.writeByte((byte)0);
		}else {
			vos.writeByte((byte)1);
			msgs1.write(vos);
		}
		if(msgs2 == null) {
			vos.writeByte((byte)0);
		}else {
			vos.writeByte((byte)1);
			msgs2.write(vos);
		}
  }

	public static IValue createFrom(ValueInputStream vis) throws IOException {
		// TODO Auto-generated method stub
		CCAction pre = CCAction.createFrom(vis);
		IValue msgs1 = null, msgs2 = null;
		byte hasMsgs1 = vis.readByte();
		if(hasMsgs1 == 1) {
			msgs1 = vis.read();
		}
		byte hasMsgs2 = vis.readByte();
		if(hasMsgs2 == 1) {
			msgs2 = vis.read();
		}
		return new CCState(pre, msgs1, msgs2);
	}

}
	
