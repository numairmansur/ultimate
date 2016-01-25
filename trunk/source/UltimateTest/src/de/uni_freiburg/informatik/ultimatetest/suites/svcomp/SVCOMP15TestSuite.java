/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.suites.svcomp;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP15TestSuite extends AbstractSVCOMPTestSuite {

	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 30 * 1000;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return 45;
	}

	@Override
	protected List<TestDefinition> getTestDefinitions() {
		List<TestDefinition> rtr = new ArrayList<>();
		//@formatter:off

		// available sets:
		//Arrays
		//BitVectors.set
		//Concurrency.set
		//ControlFlowInteger.set
		//DeviceDrivers64.set
		//DriverChallenges.set
		//ECA.set
		//Floats.set
		//HeapManipulation.set
		//Loops.set
		//MemorySafety.set
		//ProductLines.set
		//Recursive.set
		//Sequentialized.set
		//Simple.set
		//Stateful.set
		//Termination-crafted.set
		//Termination-ext.set
		//@formatter:on

		/* Automizer */
//		rtr.add(getTestDefinitionFromExamples("Arrays", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//
//		rtr.add(getTestDefinitionFromExamples("BitVectors", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ECA", "AutomizerC.xml", "svcomp2015/svComp-32bit-precise-Automizer.epf",
//				getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Loops", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLines", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "AutomizerC.xml",
//				"svcomp2015/svComp-64bit-simple-Automizer.epf", getTimeout()));
//
//		rtr.add(getTestDefinitionFromExamples("HeapManipulation", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//
//		rtr.add(getTestDefinitionFromExamples("MemorySafety", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-memsafety-Automizer.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("Recursive", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("Sequentialized", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
//
//		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-simple-Automizer.epf", getTimeout()));

//		rtr.add(getTestDefinitionFromExamples("Concurrency", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-Automizer.epf", getTimeout()));
		
		
		
//		/* Kojak */
//		rtr.add(getTestDefinitionFromExamples("Arrays", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ECA", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Loops", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLines", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Recursive", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Sequentialized", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-64bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Simple", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("MemorySafety", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-memsafety-BE-Kojak.epf.epf", getTimeout()));

		/* Impulse */
//		rtr.add(getTestDefinitionFromExamples("Arrays", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("BitVectors", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ECA", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Loops", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLine", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//
//		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-64bit-precise-BE-Impulse.epf", getTimeout()));
//
//		rtr.add(getTestDefinitionFromExamples("HeapManipulation", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//
//		rtr.add(getTestDefinitionFromExamples("MemorySafety", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-memsafety-BE-Impulse.epf.epf", getTimeout()));
//
//		
//		rtr.add(getTestDefinitionFromExamples("Recursive", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("Sequentialized", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("Simple", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("Concurrency", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));

		/* Abstract Interpretation */
		rtr.add(getTestDefinitionFromExamples("Loops-validate", "AbstractInterpretationv2C.xml",
		        "ai/AIv2_INT.epf", getTimeout()));
		
		return rtr;
	}

}
