AlleAlle - A Bounded Relational Model Finder with Data <img src="allealle_logo.svg" alt="AlleAlle Logo" width="100px"/>
=======================================================================================================================

Many problems have relational (graph-like) structures. Relational model finders help you define and solve these problems in a natural way. <sup>1</sup> *AlleAlle* is such a relational model finder.

*AlleAlle* offers a language which combines first order logic (FOL) and Codd's relational algebra (think databases and SQL) allowing for efficient encodings of many relational problems (take a look at the [examples](https://github.com/cwi-swat/allealle/tree/master/examples)). Next to that, *AlleAlle* allows for the expression of optimization objectives making it possible to solve optimization problems as well.

*AlleAlle* is implemented in Rascal and its language is integrated with Eclipse. Next to that it uses Microsofts Z3 SMT solver as a backend.

Prerequisits
------------

Be sure the following is installed and configured on your system:

-	[Java JDK](http://www.oracle.com/technetwork/java/javase/downloads/index.html) *Version 8*. Rascal does not work correctly with Java versions higher than 8!
-	[Microsofts Z3 SMT solver](https://github.com/Z3Prover/z3)
-	[Eclipse IDE](https://www.eclipse.org/downloads/packages/release/2020-06/r/eclipse-ide-rcp-and-rap-developers). Download the 'RCP and RAP' version. Please make sure that you download the 06-2020 version. Higher versions of Eclipse depend on Java 11 or higher which in turn clashes with Rascal's Java 8 requirement. Eclipse 06-2020 depends on Java 8.
-	[Rascal](https://www.rascal-mpl.org). Be sure to install the *stable* version in Eclipse using the following url: https://update.rascal-mpl.org/stable/

You need to add the following option to the `eclipse.ini` file of your Eclipse installation: `-Dsolver.z3.path=<path to your local Z3 executable>`. The default path that is used if no path is configured is: `/usr/bin/`

Running *AlleAlle*
------------------

AlleAlle can be installed as *Eclipse Plugin*. After you have succesfully installed Rascal and made sure it is working correctly you can install AlleAlle using the following steps:
- In Eclipse, go to `Help` -> `Install New Software...`.
- Enter ` https://update.rascal-mpl.org/libs/` into the `Work with` text field and hit enter.
- Select the `allealle_feature` from the `Rascal Libraries` list
- Keep clicking `Next` until the installation is done. You can select `Yes` if you see the warning `Are you sure that you want to install unsigned software...`.
- Restart Eclipse to finish the installation. 

After you have restarted Eclipse *AlleAlle* should be registered and usable. You can check this by opening an `*.alle` file in the IDE. For instance, create a new file `thief.alle` and copy the content from [examples/relational/thief.alle](https://raw.githubusercontent.com/cwi-swat/allealle/master/examples/relational/thief.alle) in the file. If all is well this file will show with syntax highlighting. By right-clicking on the specification you can select the option `Check and Visualize`. This starts the translation from AlleAlle to SMT and calls Z3 to solve the generated formula. The result should be a visualization of a found solution in 'table mode' showing who is the thief.

It is probably a good idea to add the `Console` view to your perspective since most of AlleAlle's running output is logged here. You can open this view by selecting `Window` -> `Show View` -> `Other...` and selecting `Console`. 

Troubleshooting
---------------

**Z3 cannot be found:** If running `Check and Visualize` command does not seem to work (because nothing is happening), check the `Error Log` (`Windows` -> `Show View` -> `Other...`, select `Error Log`) for errors. Big change that there is an error stating that Z3 could not be found. If this is the case please make sure that Z3 is installed correctly on your system and that you correctly configured the `-Dsolver.z3.path` property in your `eclipse.ini` file. The property should point to the directory of the Z3 executable.

<sub>1) A nice overview of problems and problem domains where relational model finders have been used can be found at http://alloytools.org/citations/case-studies.html.</sub>
