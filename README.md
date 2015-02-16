# ECMA-262 [![Build Status][travis-badge]][travis-badge-url]

Haskell ECMA 262 interpreter

This package installs an executable ecma262 which takes a filename as its only argument and interprets its content.

To test the interpreter in GHCI, install the package and then use the function runJavaScript source
from Language.JavaScript. 
A small host environment is provided in Language.JavaScript.Host.Console which adds the function console.log.
Use runHostedJavaScript source console from Language.JavaScript to try this.

[travis-badge]: https://travis-ci.org/fabianbergmark/ECMA-262.svg?branch=master
[travis-badge-url]: https://travis-ci.org/fabianbergmark/ECMA-262
