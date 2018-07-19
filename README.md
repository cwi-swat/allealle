AlleAlle - A Bounded Relational Model Finder with Data <img src="https://github.com/cwi-swat/allealle/blob/master/allealle_logo.svg" alt="AlleAlle Logo" width="100px"/>
========================================================================================================================================================================

Many problems have relational (graph-like) structures. Relational model finders help you define and solve these problems in a natural way. <sup>1</sup> AlleAlle is such a relational model finder.

AlleAlle offers a language which combines first order logic (FOL) and Codd's relational algebra (think databases and SQL) allowing for efficient encodings of many relational problems (take a look at the [examples](https://github.com/cwi-swat/allealle/tree/master/examples)). Next to that, AlleAlle allows for the expression of optimization objectives making it possible to solve optimization problems as well.

AlleAlle is implemented in Rascal and its language is integrated with Eclipse. Next to that it uses Microsofts Z3 SMT solver as a backend.

Prerequisits
------------

Be sure the following is installed and configured on your system:

-	[Java JDK](http://www.oracle.com/technetwork/java/javase/downloads/index.html) Version 8 or higher
-	[Microsofts Z3 SMT solver](https://github.com/Z3Prover/z3)
-	[Eclipse IDE](http://www.eclipse.org/). Download the 'RCP and RAP' version.
-	[Rascal](https://www.rascal-mpl.org). Be sure to install the unstable version in Eclipse using the following url: https://update.rascal-mpl.org/unstable/

You need to add the following option to the `eclipse.ini` file of your Eclipse installation: `-Dsolver.z3.path=<path to your local Z3 executable>`

<sub>1) A nice overview of problems and problem domains where relational model finders have been used can be found [here](http://alloytools.org/citations/case-studies.html).</sub>
