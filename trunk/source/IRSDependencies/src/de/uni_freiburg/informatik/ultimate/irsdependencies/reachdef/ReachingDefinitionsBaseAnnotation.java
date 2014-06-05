package de.uni_freiburg.informatik.ultimate.irsdependencies.reachdef;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;

public abstract class ReachingDefinitionsBaseAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;
	
	public static final String AnnotationName = "ReachingDefinition";

	@SuppressWarnings("unchecked")
	public static <T extends ReachingDefinitionsBaseAnnotation> T getAnnotation(IElement element) {
		if (!element.hasPayload()) {
			return null;
		}
		if (!element.getPayload().hasAnnotation()) {
			return null;
		}
		return (T) element.getPayload().getAnnotations().get(AnnotationName);
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] { "Def", "Use" };
	}

	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "Def":
			return prettyPrintDefUse(getDefs());
		case "Use":
			return prettyPrintDefUse(getUse());
		default:
			return null;
		}
	}
	
	protected abstract HashMap<String, HashSet<Statement>> getDefs();
	protected abstract HashMap<String, HashSet<Statement>> getUse();

	public void annotate(IElement node) {
		node.getPayload().getAnnotations().put(AnnotationName, this);
	}

	public ReachingDefinitionsBaseAnnotation() {
		super();
	}

	private String prettyPrintDefUse(HashMap<String, HashSet<Statement>> map) {
		if (map.isEmpty()) {
			return "Empty";
		}
	
		StringBuilder sb = new StringBuilder();
	
		for (String s : map.keySet()) {
			sb.append(s).append(": {");
			HashSet<Statement> set = map.get(s);
			if (set.isEmpty()) {
				continue;
			}
			for (Statement stmt : map.get(s)) {
				sb.append(BoogieStatementPrettyPrinter.print(stmt)).append(", ");
			}
			sb.delete(sb.length() - 2, sb.length());
			sb.append("}, ");
		}
	
		sb.delete(sb.length() - 2, sb.length());
		return sb.toString();
	}

}