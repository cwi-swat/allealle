module util::Memory

@javaClass{util.Memory}
java int getFreeMemory();

@javaClass{util.Memory}
java int getTotalMemory();

@javaClass{util.Memory}
java int getMaxMemory();

int getUsedMemory() = getTotalMemory() - getFreeMemory();