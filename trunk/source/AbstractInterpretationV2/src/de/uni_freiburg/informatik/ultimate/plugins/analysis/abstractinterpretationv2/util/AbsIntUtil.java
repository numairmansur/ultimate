/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class AbsIntUtil {

	/**
	 * Write predicates created by AI to a file.
	 * 
	 * @param preds
	 * @param filePath
	 */
	public static void dumpToFile(final Map<CodeBlock, Map<ProgramPoint, Term>> preds, final String filePath) {
		final StringBuilder sb = new StringBuilder();
		for (final Entry<CodeBlock, Map<ProgramPoint, Term>> entry : preds.entrySet()) {
			if (entry.getValue().isEmpty()) {
				continue;
			}
			sb.append(entry.getKey().toString()).append("\n");
			for (final Entry<ProgramPoint, Term> runPreds : entry.getValue().entrySet()) {
				sb.append(" * ").append(runPreds.getValue()).append("\n");
			}
		}
		if (sb.length() == 0) {
			sb.append("No preds :(\n");
		}

		sb.append("\n\n");
		try {
			final BufferedWriter bw = new BufferedWriter(new FileWriter(filePath, true));
			bw.append(sb);
			bw.close();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
}
