// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:18:01 PST by lamport
//      modified on Fri Aug 10 15:09:53 PDT 2001 by yuanyu

package tlc2.value;

import java.io.IOException;
import java.math.BigInteger;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.FingerprintException;
import util.Assert;
import util.UniqueString;

public class SetOfRcdsValue extends SetOfFcnsOrRcdsValue implements Enumerable {
  public final UniqueString[] names;      // The names of the fields.
  public final Value[] values;            // The values of the fields.
  protected SetEnumValue rcdSet;

  /* Constructor */
  public SetOfRcdsValue(UniqueString[] names, Value[] values, boolean isNorm) {
	  assert names.length == values.length; // see tlc2.tool.Tool.evalAppl(OpApplNode, Context, TLCState, TLCState, int) case for OPCODE_sor
    this.names = names;
    this.values = values;
    this.rcdSet = null;
    if (!isNorm) {
      this.sortByNames();
    }
  }

  public final byte getKind() { return SETOFRCDSVALUE; }

  public final int compareTo(Object obj) {
    try {
      this.convertAndCache();
      return this.rcdSet.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      if (obj instanceof SetOfRcdsValue) {
        SetOfRcdsValue rcds = (SetOfRcdsValue)obj;

        boolean isEmpty1 = this.isEmpty();
        if (isEmpty1) { return rcds.isEmpty(); }
        if (rcds.isEmpty()) { return isEmpty1; }

        if (this.names.length != rcds.names.length) {
          return false;
        }
        for (int i = 0; i < this.names.length; i++) {
          if (!this.names[i].equals(rcds.names[i]) ||
              !this.values[i].equals(rcds.values[i])) {
            return false;
          }
        }
        return true;
      }
      this.convertAndCache();
      return this.rcdSet.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(Value elem) {
    try {
      RecordValue rcd = elem.toRcd();
      if (rcd == null) {
        if (elem instanceof ModelValue)
           return ((ModelValue) elem).modelValueMember(this) ;
        Assert.fail("Attempted to check if non-record\n" + elem + "\nis in the" +
        " set of records:\n" + ppr(this.toString()));
      }
      rcd.normalize();
      if (this.names.length != rcd.names.length) {
        return false;
      }
      for (int i = 0; i < this.names.length; i++) {
        if ((!this.names[i].equals(rcd.names[i])) ||
          (!this.values[i].member(rcd.values[i]))) {
          return false;
        }
      }
      return true;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      for (int i = 0; i < this.values.length; i++) {
        if (!this.values[i].isFinite()) return false;
      }
      return true;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT to the set of records:\n" +
        ppr(this.toString()));
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT to the set of records:\n" +
        ppr(this.toString()));
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      long sz = 1;
      for (int i = 0; i < this.values.length; i++) {
        sz *= this.values[i].size();
        if (sz < -2147483648 || sz > 2147483647) {
          Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
                ppr(this.toString()));
        }
      }
      return (int)sz;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	protected boolean needBigInteger() {
		long sz = 1;
		for (int i = 0; i < values.length; i++) {
			sz *= values[i].size();
			if (sz < -2147483648 || sz > 2147483647) {
				return true;
			}
		}
		return false;
	}

  public final boolean isNormalized() {
    try {
      if (this.rcdSet == null || this.rcdSet == DummyEnum) {
        for (int i = 0; i < this.names.length; i++) {
          if (!this.values[i].isNormalized()) {
            return false;
          }
        }
        return true;
      }
      return this.rcdSet.isNormalized();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value normalize() {
    try {
      if (this.rcdSet == null || this.rcdSet == DummyEnum) {
        for (int i = 0; i < this.names.length; i++) {
          this.values[i].normalize();
        }
      }
      else {
        this.rcdSet.normalize();
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final void deepNormalize() {
	    try {
      for (int i = 0; i < values.length; i++) {
          values[i].deepNormalize();
        }
        if (rcdSet == null) {
          rcdSet = DummyEnum;
        }
        else if (rcdSet != DummyEnum) {
          rcdSet.deepNormalize();
        }
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
  }

  private final void sortByNames() {
    for (int i = 1; i < this.names.length; i++) {
      int cmp = this.names[0].compareTo(this.names[i]);
      if (cmp == 0) {
        Assert.fail("Field name " + this.names[0] + " occurs multiple times" +
              " in set of records.");
      }
      else if (cmp > 0) {
        UniqueString ts = this.names[0];
        this.names[0] = this.names[i];
        this.names[i] = ts;
        Value tv = this.values[0];
        this.values[0] = this.values[i];
        this.values[i] = tv;
      }
    }
    for (int i = 2; i < this.names.length; i++) {
      int j = i;
      UniqueString st = this.names[i];
      Value val = this.values[i];
      int cmp;
      while ((cmp = st.compareTo(this.names[j-1])) < 0) {
        this.names[j] = this.names[j-1];
        this.values[j] = this.values[j-1];
        j--;
      }
      if (cmp == 0) {
        Assert.fail("Field name " + this.names[i] + " occurs multiple times" +
              " in set of records.");
      }
      this.names[j] = st;
      this.values[j] = val;
    }
  }

  public final boolean isDefined() {
    try {
      boolean isDefined = true;
      for (int i = 0; i < this.values.length; i++) {
        isDefined = isDefined && this.values[i].isDefined();
      }
      return isDefined;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    try {
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    try {
      this.convertAndCache();
      return this.rcdSet.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value permute(MVPerm perm) {
    try {
      this.convertAndCache();
      return this.rcdSet.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void convertAndCache() {
    if (this.rcdSet == null) {
      this.rcdSet = this.toSetEnum();
    }
    else if (this.rcdSet == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
        if (this.rcdSet == DummyEnum) {
          val = this.toSetEnum();
          val.deepNormalize();
        }
      }
      synchronized(this) {
        if (this.rcdSet == DummyEnum) { this.rcdSet = val; }
      }
    }
  }

  @Override
  public final SetEnumValue toSetEnum() {
      if (this.rcdSet != null && this.rcdSet != DummyEnum) {
        return this.rcdSet;
      }
      ValueVec vals = new ValueVec();
      ValueEnumeration Enum = this.elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      return new SetEnumValue(vals, this.isNormalized());
  }

  @Override
  public final void write(final ValueOutputStream vos) throws IOException {
	  rcdSet.write(vos);
  }

  /* The string representation of the value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      boolean unlazy = expand;
      try {
        if (unlazy) {
          long sz = 1;
          for (int i = 0; i < this.values.length; i++) {
            sz *= this.values[i].size();
            if (sz < -2147483648 || sz > 2147483647) {
              unlazy = false;
              break;
            }
          }
          unlazy = sz < TLCGlobals.enumBound;
        }
      }
      catch (Throwable e) { unlazy = false; }

      if (unlazy) {
        Value val = this.toSetEnum();
        return val.toString(sb, offset);
      }
      else {
        sb.append("[");
        int len = this.names.length;
        if (len != 0) {
          sb.append(names[0] + ": ");
          this.values[0].toString(sb, offset);
        }
        for (int i = 1; i < len; i++) {
          sb.append(", ");
          sb.append(names[i] + ": ");
          this.values[i].toString(sb, offset);
        }
        sb.append("]");
        return sb;
      }
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final ValueEnumeration elements() {
    try {
      if (this.rcdSet == null || this.rcdSet == DummyEnum) {
        return new Enumerator();
      }
      return this.rcdSet.elements();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  final class Enumerator implements ValueEnumeration {
    private ValueEnumeration[] enums;
    private Value[] currentElems;
    private boolean isDone;

    public Enumerator() {
      this.enums = new ValueEnumeration[values.length];
      this.currentElems = new Value[values.length];
      this.isDone = false;
      for (int i = 0; i < values.length; i++) {
        if (values[i] instanceof Enumerable) {
          this.enums[i] = ((Enumerable)values[i]).elements();
          this.currentElems[i] = this.enums[i].nextElement();
          if (this.currentElems[i] == null) {
            this.enums = null;
            this.isDone = true;
            break;
          }
        }
        else {
          Assert.fail("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn]," +
                "\nbut can't enumerate the value of the `" + names[i] + "' field:\n" +
                ppr(values[i].toString()));
        }
      }
    }

    public final void reset() {
      if (this.enums != null) {
        for (int i = 0; i < this.enums.length; i++) {
          this.enums[i].reset();
          this.currentElems[i] = this.enums[i].nextElement();
        }
        this.isDone = false;
      }
    }

    public final Value nextElement() {
      if (this.isDone) return null;
      Value[] elems = new Value[this.currentElems.length];
      for (int i = 0; i < elems.length; i++) {
        elems[i] = this.currentElems[i];
      }
      for (int i = elems.length-1; i >= 0; i--) {
        this.currentElems[i] = this.enums[i].nextElement();
        if (this.currentElems[i] != null) break;
        if (i == 0) {
          this.isDone = true;
          break;
        }
        this.enums[i].reset();
        this.currentElems[i] = this.enums[i].nextElement();
      }
      return new RecordValue(names, elems, true);
    }

  }

	@Override
	protected tlc2.value.SetOfFcnsOrRcdsValue.SubsetEnumerator getSubsetEnumerator(int k, int n) {
		return new SubsetEnumerator(k, n);
	}
	
	class SubsetEnumerator extends SetOfFcnsOrRcdsValue.SubsetEnumerator {
		
		private final SetEnumValue[] convert;
		private final int[] rescaleBy;

		SubsetEnumerator(final int k, final int n) {
			super(k, n);
			
			convert = new SetEnumValue[values.length];
			rescaleBy = new int[values.length];
			
			int numElems = 1; // 1 to avoid div by zero in elementAt
			for (int i = values.length - 1; i >= 0; i--) {
				convert[i] = values[i].toSetEnum();
				rescaleBy[i] = numElems;
				numElems *= convert[i].elems.size();
			}
		}

		protected RecordValue elementAt(final int idx) {
			assert 0 <= idx && idx < size();
			
			final Value[] val = new Value[names.length];
			for (int i = 0; i < val.length; i++) {
				final SetEnumValue sev = convert[i];
				final int mod = sev.elems.size();
				
				final int rescaledIdx = (int) Math.floor(idx / rescaleBy[i]);
				final int elementAt = rescaledIdx % mod;
				
				val[i] = sev.elems.elementAt(elementAt);
			}
			return new RecordValue(names, val, false);
		}
	}
	
	@Override
	protected BigIntegerSubsetEnumerator getBigSubsetEnumerator(int k) {
		return new BigIntegerSubsetEnumerator(k);
	}
	
	class BigIntegerSubsetEnumerator extends SetOfFcnsOrRcdsValue.BigIntegerSubsetEnumerator {
		
		private final SetEnumValue[] convert;
		private final BigInteger[] rescaleBy;
		
		public BigIntegerSubsetEnumerator(final int k) {
			super(k);
			
			convert = new SetEnumValue[values.length];
			rescaleBy = new BigInteger[values.length];
			
			BigInteger numElems = BigInteger.ONE; // 1 to avoid div by zero in elementAt
			for (int i = values.length - 1; i >= 0; i--) {
				convert[i] = values[i].toSetEnum();
				rescaleBy[i] = numElems;
				numElems = numElems.multiply(BigInteger.valueOf(convert[i].elems.size()));
			}
			
			// The size of the (enumerated) SetOfFcnsOrRcdsValue needs BigInteger.
			this.sz = numElems;
		}

		@Override
		protected Value elementAt(final BigInteger idx) {
			final Value[] val = new Value[names.length];
			for (int i = 0; i < val.length; i++) {
				final SetEnumValue sev = convert[i];
				final int mod = sev.elems.size();

				final BigInteger d = idx.divide(rescaleBy[i]);
				final BigInteger m = d.mod(BigInteger.valueOf(mod));
				final int elementAt = m.intValueExact();

				val[i] = sev.elems.elementAt(elementAt);
			}
			return new RecordValue(names, val, false);
		}
	}
}
