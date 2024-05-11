medrina
===

[![Maven Central](https://img.shields.io/maven-central/v/com.io7m.medrina/com.io7m.medrina.svg?style=flat-square)](http://search.maven.org/#search%7Cga%7C1%7Cg%3A%22com.io7m.medrina%22)
[![Maven Central (snapshot)](https://img.shields.io/nexus/s/com.io7m.medrina/com.io7m.medrina?server=https%3A%2F%2Fs01.oss.sonatype.org&style=flat-square)](https://s01.oss.sonatype.org/content/repositories/snapshots/com/io7m/medrina/)
[![Codecov](https://img.shields.io/codecov/c/github/io7m-com/medrina.svg?style=flat-square)](https://codecov.io/gh/io7m-com/medrina)
![Java Version](https://img.shields.io/badge/21-java?label=java&color=e6c35c)

![com.io7m.medrina](./src/site/resources/medrina.jpg?raw=true)

| JVM | Platform | Status |
|-----|----------|--------|
| OpenJDK (Temurin) Current | Linux | [![Build (OpenJDK (Temurin) Current, Linux)](https://img.shields.io/github/actions/workflow/status/io7m-com/medrina/main.linux.temurin.current.yml)](https://www.github.com/io7m-com/medrina/actions?query=workflow%3Amain.linux.temurin.current)|
| OpenJDK (Temurin) LTS | Linux | [![Build (OpenJDK (Temurin) LTS, Linux)](https://img.shields.io/github/actions/workflow/status/io7m-com/medrina/main.linux.temurin.lts.yml)](https://www.github.com/io7m-com/medrina/actions?query=workflow%3Amain.linux.temurin.lts)|
| OpenJDK (Temurin) Current | Windows | [![Build (OpenJDK (Temurin) Current, Windows)](https://img.shields.io/github/actions/workflow/status/io7m-com/medrina/main.windows.temurin.current.yml)](https://www.github.com/io7m-com/medrina/actions?query=workflow%3Amain.windows.temurin.current)|
| OpenJDK (Temurin) LTS | Windows | [![Build (OpenJDK (Temurin) LTS, Windows)](https://img.shields.io/github/actions/workflow/status/io7m-com/medrina/main.windows.temurin.lts.yml)](https://www.github.com/io7m-com/medrina/actions?query=workflow%3Amain.windows.temurin.lts)|

## medrina

The `medrina` package implements a generic system for implementing role/attribute
mandatory access control systems.

## Features

* Role-based access control for security policies.
* Formal specification with proofs of correctness.
* High coverage test suite (100%, minus an unreachable private constructor).
* [OSGi-ready](https://www.osgi.org/).
* [JPMS-ready](https://en.wikipedia.org/wiki/Java_Platform_Module_System).
* ISC license.

## Usage

See the [documentation](https://www.io7m.com/software/medrina/).

