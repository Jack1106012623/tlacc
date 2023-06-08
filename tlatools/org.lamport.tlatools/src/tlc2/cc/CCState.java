package tlc2.cc;

import tlc2.cc.CCAction.Type;
import tlc2.value.IValue;
import tlc2.value.impl.SetEnumValue;

public class CCState implements Cloneable {
	/**
	 * ccIter is used to indicate the current position in the CC rounds and to determine the next permitted actions.
	 */
	private CCAction pre;
	/**
	 * msgs1 stores current round's messages and msgs2 = msg1 \cap X where X is Rcv_U_Send's messages.
	 */
	private IValue msgs1;
	private IValue msgs2;
	
	public static CCState Empty = null;
	public static void setEmpty(CCState ccstate) {
		Empty = ccstate;
	}
	
	public CCState(CCAction pre) {
		this.pre = pre;
		this.msgs1 = null;
		this.msgs2 = null;
	}
	
	private CCState(CCAction pre, IValue msgs1, IValue msgs2) {
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
	public String toString() {
		String str1 = "CCIterator: " + pre.toString();
		str1 += msgs1 == null ? ", msgs1 = null" : ", msgs1 = " + msgs1.size();
		str1 += msgs2 == null ? ", msgs2 = null" : ", msgs2 = " + msgs2.size();

		return str1;
	}
	
	
	
	// Only need to hash ccIter.
	public long fingerPrint() {
		return this.pre.fingerPrint();
	}
	
}
	
