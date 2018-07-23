AlleAlle - A Bounded Relational Model Finder with Data <img src="allealle_logo.svg" alt="AlleAlle Logo" width="100px"/>
=======================================================================================================================

Many problems have relational (graph-like) structures. Relational model finders help you define and solve these problems in a natural way. <sup>1</sup> *AlleAlle* is such a relational model finder.

*AlleAlle* offers a language which combines first order logic (FOL) and Codd's relational algebra (think databases and SQL) allowing for efficient encodings of many relational problems (take a look at the [examples](https://github.com/cwi-swat/allealle/tree/master/examples)). Next to that, *AlleAlle* allows for the expression of optimization objectives making it possible to solve optimization problems as well.

*AlleAlle* is implemented in Rascal and its language is integrated with Eclipse. Next to that it uses Microsofts Z3 SMT solver as a backend.

Prerequisits
------------

Be sure the following is installed and configured on your system:

-	[Java JDK](http://www.oracle.com/technetwork/java/javase/downloads/index.html) Version 8 or higher
-	[Microsofts Z3 SMT solver](https://github.com/Z3Prover/z3)
-	[Eclipse IDE](http://www.eclipse.org/). Download the 'RCP and RAP' version.
-	[Rascal](https://www.rascal-mpl.org). Be sure to install the unstable version in Eclipse using the following url: https://update.rascal-mpl.org/unstable/

You need to add the following option to the `eclipse.ini` file of your Eclipse installation: `-Dsolver.z3.path=<path to your local Z3 executable>`

Running *AlleAlle*
------------------

After cloning this repository start up Eclipse (preferably with a fresh workspace, not mandatory). Once Eclipse is running choose `File` -> `Import` and select `Existing Projects into Workspace`. Select the directory where you cloned the *AlleAlle* repository.

Once Eclipse is done importing the project, restart Eclipse and open the same workspace. On restart Rascal automatically registers any language defined by an opened project. Because *AlleAlle* is defined as a language it will be automatically registered with Eclipse too.

After you have restarted Eclipse *AlleAlle* should be registered and usable. You can check this by opening an `*.alle` file in the IDE. For instance, open `examples/relational/thief.alle`. If all is well this file will show with syntax highlighting. By right-clicking on the specification you can select the option `Check and Visualize`. This starts the translation from AlleAlle to SMT and calls Z3 to solve the generated formula. The result should be a visualization of a found solution in 'table mode' showing who is the thief.

Troubleshooting
---------------

**Syntax highlighting does not work:** Probably the language definition of *AlleAlle* was not loaded properly. You can check this by opening up the 'Console' view (`Window` -> `Show View` -> `Other...`, select `Console`). If *AlleAlle* got registered correctly you will see the message `Dynamically registering language AlleAlle`. If you don't see this message it means the *AlleAlle* did not get registered. To fix this you can register *AlleAlle* manually. In the `Rascal Navigator` go to `src/ide/Plugin.rsc`. Right-click on the file and select `Run As` -> `Rascal Application`. You will see a new `Terminal` window in the bottom half of the IDE. After the terminal started and the cursor is blinking you can hit the `Reload language` button ![refresh](language_refresh.png). This should register *AlleAlle* with the IDE. Check the console for the previously described message.

**Z3 cannot be found:** If running `Check and Visualize` command does not seem to work (because nothing is happening), check the `Error Log` (`Windows` -> `Show View` -> `Other...`, select `Error Log`) for errors. Big change that there is an error stating that Z3 could not be found. If this is the case please make sure that Z3 is installed correctly on your system and that you correctly configured the `-Dsolver.z3.path` property in your `eclipse.ini` file. The property should point to the directory of the Z3 executable.

<sub>1) A nice overview of problems and problem domains where relational model finders have been used can be found at http://alloytools.org/citations/case-studies.html.</sub>
