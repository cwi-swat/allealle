package util;

import io.usethesource.vallang.IInteger;
import io.usethesource.vallang.IValueFactory;

public class Memory {

	private final IValueFactory values;
	
	public Memory(IValueFactory values){
		super();
		
		this.values = values;
	}
	
	public IInteger getFreeMemory() {
		return values.integer(Runtime.getRuntime().freeMemory());
	}

	public IInteger getTotalMemory() {
		return values.integer(Runtime.getRuntime().totalMemory());
	}

	public IInteger getMaxMemory() {
		return values.integer(Runtime.getRuntime().maxMemory());
	}
	
}
