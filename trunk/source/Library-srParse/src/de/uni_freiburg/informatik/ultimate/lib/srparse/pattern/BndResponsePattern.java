package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class BndResponsePattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(1); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		CDD s_cdd = cdds.get(0);
		
		pea = peaTransformator.bndResponsePattern(p_cdd, q_cdd, r_cdd, s_cdd, duration, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that if \""+cdds.get(1)+"\" holds, then \""+cdds.get(0)+"\" holds after at most \""+duration+"\" time units";
		
		return res;
	}
}
