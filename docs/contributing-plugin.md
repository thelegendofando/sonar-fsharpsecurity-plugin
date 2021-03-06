# Building, Testing and Debugging the SonarQube plugin

This page documents how to develop with the Java side of the plugin.

See [here for building, testing and debugging the F# analyzer](contributing-analyzer.md).

## How the plugin works

The plugin is a mix of Java (under `sonar-fsharpsecurity-plugin`) and F# (under `SonarAnalyzer.FSharp`).  

The plugin itself is written in Java and is loaded when `sonar-scanner` is used. The way it works is that Sonar provides a number of abstract classes which
the plugin then implements. 

* Sonar asks the plugin what file extensions it wants. The plugin returns `.fs` and `.fsproj`, etc.
* Sonar asks the plugin what rules it supports. In this case, the plugin returns the list using an XML file generated by the F# executable called `FsSolarRunner.exe` (using the `--export` option).
* The Sonar server may know that the user has asked for some of these rules not to run (to avoid the same errors over and over again)
* Sonar then passes the rules and the files into the plugin 
* The plugin analyzes those files. In this case the plugin:
  * writes those rules and files to an XML file
  * then executes the F# executable (`FsSolarRunner.exe`) passing that input file as parameter
  * the F# exe dumps out the results as files.
  * the plugin then reads these files in to memory
* Finally the plugin returns them to the Solar framework which stores them in the database associated with the server.

## Installing Java and Maven on Windows

To install on Windows, I recommend using the [Chocolatey package manager](https://chocolatey.org/).

You'll need to install:

* [OpenJDK](https://chocolatey.org/packages/openjdk) using `choco install openjdk`
* For building, you'll also need [Maven](https://chocolatey.org/packages/maven) using `choco install maven`

## Installing Java and Maven on other platforms

Use your preferred package manager, such as `apt-get`.


## Getting the code

* Clone [this repository](https://github.com/swlaschin/sonar-fsharpsecurity-plugin.git)
* Download sub-modules `git submodule update --init --recursive`

## To build and test

To build the Java plugin .jar file (from the root):

```
mvn clean install
```

To run the Java unit tests:

```
mvn clean test
```

To create the .jar file that can be copied to the SonarQube plugins directory:

```
mvn clean package
```

The .jar file is output to `\sonar-fsharpsecurity-plugin\target`

To run the same script that AppVeyor uses:

```
mvn -Dconfiguration=Release clean install
```

## Developing with VS Code

Install:

* Language Support for Java by Red Hat -- [redhat.java](https://marketplace.visualstudio.com/items?itemName=redhat.java)
* Microsoft Debugger for Java -- [vscjava.vscode-java-debug](https://marketplace.visualstudio.com/items?itemName=vscjava.vscode-java-debug)

To debug a plugin, see [the instructions on the SonarQube site](https://docs.sonarqube.org/latest/extend/developing-plugin/)

## Developing with Eclipse or IntelliJ

When working with Eclipse or IntelliJ please follow the [sonar guidelines](https://github.com/SonarSource/sonar-developer-toolset)

## Understanding the Sonar Plugin API

See http://javadocs.sonarsource.org/7.9.1/apidocs/


## Contributing

Please see [Contributing Code](../CONTRIBUTING.md) for details on contributing changes back to the code.
