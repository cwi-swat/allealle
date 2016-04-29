package smt.solver;

import org.rascalmpl.interpreter.utils.RuntimeExceptionFactory;
import org.rascalmpl.value.IInteger;
import org.rascalmpl.value.IValueFactory;

public class ThreadUtil {
	public ThreadUtil(IValueFactory vf) {}
	
	public void sleep(IInteger ms) {
		try {
			Thread.sleep(ms.longValue());
		} catch (InterruptedException e) {
			throw RuntimeExceptionFactory.javaException(e, null, null);
		}
	}
}
