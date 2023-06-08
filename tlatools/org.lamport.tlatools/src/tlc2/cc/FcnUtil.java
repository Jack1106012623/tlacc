package tlc2.cc;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueVec;

public class FcnUtil implements ValueConstants {

	public FcnUtil() {
		// TODO Auto-generated constructor stub
	}

	/**
	 * @param f1
	 * @param f2
	 * @return f1 - f2 : [x \in ((DOMAIN f1) \ (DOMAIN f2)) |-> f1[x]]
	 */
	public static Value diff(Value f1, Value f2) {
		
		FcnRcdValue fcn1 = (FcnRcdValue) f1.toFcnRcd();
		FcnRcdValue fcn2 = (FcnRcdValue) f2.toFcnRcd();
		assert(fcn1.isNormalized() && fcn2.isNormalized());
		
		Value[] dom1 = fcn1.domain;
		Value[] dom2 = fcn2.domain;
		Value[] vals1 = fcn1.values;
		ValueVec dom = new ValueVec();
		ValueVec vals = new ValueVec();
		// TODO: deal with IntervalValue
		assert(dom1 != null && dom2 != null);
		
		for(int i=0,j=0;i<dom1.length;i++) {
			boolean flag = (j==dom2.length) || (j<dom2.length && !dom1[i].equals(dom2[j]));
			if(flag) {
				dom.addElement(dom1[i]);
				vals.addElement(vals1[i]);
			}else {
				j++;
			}
		}

		Value[] domain = new Value[dom.size()];
		Value[] values = new Value[dom.size()];
		for (int i = 0; i < domain.length; i++) {
			domain[i] = dom.elementAt(i);
			values[i] = vals.elementAt(i);
		}
		return new FcnRcdValue(domain, values, false);
	}

}
