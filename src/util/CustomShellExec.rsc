@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Mark Hills - Mark.Hills@cwi.nl (CWI)}

@doc{
.Synopsis
Execute and manage external processes.
}
module util::CustomShellExec

@doc{
.Synopsis
Start a new external process.
.Description

#   Start a new external process.
#   Start a new external process in a given working directory.
#   Start a new external process with the given arguments.
#   Start a new external process with the given arguments in the given working directory.
#   Start a new external process with the given environment variables.
#   Start a new external process with the given environment variables in the given working directory.
#   Start a new external process with the given arguments and environment variables.
#   Start a new external process with the given arguments and environment variables in the given working directory.

}
@javaClass{util.CustomShellExec}
public java PID createProcess(str processCommand, loc workingDir=|cwd:///|, list[str] args = [], map[str,str] envVars = ());

@doc{
.Synopsis
start, run and kill an external process returning its output as a string.
}
public str exec(str processCommand, loc workingDir=|cwd:///|, list[str] args = [], map[str,str] env = ()) {
   pid = createProcess(processCommand, workingDir=workingDir, args=args, envVars=env);
   result = readEntireStream(pid);
   killProcess(pid);
   return result;
}

@doc{
.Synopsis
Kill a running process, or a zombie process (a process which is not alive yet not killed)
}
@javaClass{util.CustomShellExec}
public java void killProcess(PID processId, bool force=false);

@doc{
.Synopsis
Check whether a process is still alive
}
@javaClass{util.CustomShellExec}
public java bool isAlive(PID processId);

@doc{
.Synopsis
Check whether a process is still registered but not actually running anymore. A zombie process may be cleaned up using killProcess.
}
@javaClass{util.CustomShellExec}
public java bool isZombie(PID processId);


@doc{
.Synopsis
Read from an existing process's output stream. This is non-blocking.
}
@javaClass{util.CustomShellExec}
public java str readFrom(PID processId);

@doc{
.Synopsis
Read from an existing process's output stream with a given wait timeout. Some processes are a little slower in producing output. The wait is used to give the process some extra time in producing output. This is non-blocking apart from the waiting.
}
@javaClass{util.CustomShellExec}
public java str readWithWait(PID processId, int wait);


@doc{
.Synopsis
Read from an existing process's error output stream. This is non-blocking.
}
@javaClass{util.CustomShellExec}
public java str readFromErr(PID processId);

@doc{
.Synopsis
Read from an existing process's error output stream. This blocks until a full line is read and
waits for one second maximally for this line to appear.
}
@javaClass{util.CustomShellExec}
public java str readLineFromErr(PID processId, int wait=200, int maxTries=5);

@doc{
.Synopsis
Read the entire stream from an existing process's output stream. This is blocking.
}
@javaClass{util.CustomShellExec}
public java str readEntireStream(PID processId);

@doc{
.Synopsis
Read the entire error stream from an existing process's output stream. This is blocking.
}
@javaClass{util.CustomShellExec}
public java str readEntireErrStream(PID processId);

@doc{
.Synopsis
Write to an existing process's input stream.
}
@javaClass{util.CustomShellExec}
public java void writeTo(PID processId, str msg);

@doc{
.Synopsis
Process Identifiers (PID).

.Description
A PID is returned by <<createProcess>> and is required for any further interaction with the created process.
}
public alias PID = int;