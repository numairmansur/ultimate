package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class ResponseChain21Pattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(2); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		CDD s_cdd = cdds.get(1);
		CDD t_cdd = cdds.get(0);
		
		pea = peaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that if \""+cdds.get(3)+"\" holds and is succeeded by \""+cdds.get(2)+"\", then \""+cdds.get(1)+"\" eventually holds after \""+cdds.get(0)+"\"";
		
		return res;
	}
}
