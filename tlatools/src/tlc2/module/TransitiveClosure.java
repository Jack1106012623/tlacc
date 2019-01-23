// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:19:51 PST by lamport
//      modified on Tue Aug 22 16:03:24 PDT 2000 by yuanyu

package tlc2.module;

import java.util.Hashtable;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.util.Vect;
import tlc2.value.Enumerable;
import tlc2.value.ITupleValue;
import tlc2.value.IValue;
import tlc2.value.SetEnumValue;
import tlc2.value.TupleValue;
import tlc2.value.ValueConstants;
import tlc2.value.ValueEnumeration;
import tlc2.value.ValueVec;
import tlc2.value.Values;

public class TransitiveClosure implements ValueConstants
{
	public static final long serialVersionUID = 20160822L;

    /* Implement the Warshall algorithm for transitive closure. */
    public static IValue Warshall(IValue rel)
    {
        if (!(rel instanceof Enumerable))
        {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "TransitiveClosure",
                    "an enumerable set", Values.ppr(rel.toString()) });
        }
        int maxLen = 2 * rel.size();
        boolean[][] matrix = new boolean[maxLen][maxLen];
        ValueEnumeration elems = ((Enumerable) rel).elements();
        Vect<IValue> elemList = new Vect<>();
        Hashtable<IValue, Integer> fps = new Hashtable<>();
        int cnt = 0;
        IValue elem = null;
        while ((elem = elems.nextElement()) != null)
        {
            ITupleValue tv = (ITupleValue) elem.toTuple();
            if (tv == null || tv.size() != 2)
            {
                throw new EvalException(EC.TLC_MODULE_TRANSITIVE_CLOSURE, Values.ppr(elem.toString()));
            }
            IValue elem1 = tv.getElem(0);
            IValue elem2 = tv.getElem(1);
            int num1 = cnt;
            Integer num = (Integer) fps.get(elem1);
            if (num == null)
            {
                fps.put(elem1, new Integer(cnt));
                elemList.addElement(elem1);
                cnt++;
            } else
            {
                num1 = num.intValue();
            }
            int num2 = cnt;
            num = (Integer) fps.get(elem2);
            if (num == null)
            {
                fps.put(elem2, new Integer(cnt));
                elemList.addElement(elem2);
                cnt++;
            } else
            {
                num2 = num.intValue();
            }
            matrix[num1][num2] = true;
        }

        for (int y = 0; y < cnt; y++)
        {
            for (int x = 0; x < cnt; x++)
            {
                if (matrix[x][y])
                {
                    for (int z = 0; z < cnt; z++)
                    {
                        if (matrix[y][z])
                            matrix[x][z] = true;
                    }
                }
            }
        }

        ValueVec newElems = new ValueVec();
        for (int i = 0; i < cnt; i++)
        {
            for (int j = 0; j < cnt; j++)
            {
                if (matrix[i][j])
                {
                	IValue elem1 = (IValue) elemList.elementAt(i);
                	IValue elem2 = (IValue) elemList.elementAt(j);
                	IValue newElem = new TupleValue(elem1, elem2);
                    newElems.addElement(newElem);
                }
            }
        }
        return new SetEnumValue(newElems, false);
    }

}
