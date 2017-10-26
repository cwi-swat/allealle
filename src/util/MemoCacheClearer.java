package util;

import java.util.List;

import org.rascalmpl.interpreter.IEvaluatorContext;
import org.rascalmpl.interpreter.env.ModuleEnvironment;
import org.rascalmpl.interpreter.env.Pair;
import org.rascalmpl.interpreter.result.AbstractFunction;
import org.rascalmpl.interpreter.result.NamedFunction;

import io.usethesource.vallang.IBool;
import io.usethesource.vallang.ISet;
import io.usethesource.vallang.IString;
import io.usethesource.vallang.IValue;
import io.usethesource.vallang.IValueFactory;

public class MemoCacheClearer {
	
	public MemoCacheClearer(IValueFactory vf) {
		super();
	}
	
	public void clearMemoCache(ISet modules, IBool debug, IEvaluatorContext ec) {
		for (IValue mod : modules) {
			String modName = ((IString)mod).getValue();
			
			ModuleEnvironment module = ec.getHeap().getModule(modName);
			if (module != null) {
				if (debug.getValue()) {
					ec.getStdOut().println("Module " + modName + " found");
				}
				
				List<Pair<String, List<AbstractFunction>>> functions = module.getFunctions();
				for (Pair<String, List<AbstractFunction>> func : functions) {
					for (AbstractFunction f : func.getSecond()) {
						if (f instanceof NamedFunction) {
							((NamedFunction)f).clearMemoizationCache();
							if (debug.getValue()) {
								ec.getStdOut().println("Cleared the memo cache of the \'" + f.getName() + "\' function");
							}
						}
					}
				}
			} else {
				if (debug.getValue()) {
					ec.getStdOut().println("Module " + modName + " NOT found, skipping memo cache resetting");
				}
			}
		}
	}
	
	public void gc() {
		System.gc();
	}
}
