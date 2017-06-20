package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class MinDurationPattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(0); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		
		pea = peaTransformator.minDurationPattern(p_cdd, q_cdd, r_cdd, duration, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that once \""+cdds.get(0)+"\" becomes satisfied, it holds for at least \""+duration+"\" time units";
		
		return res;
	}
}
