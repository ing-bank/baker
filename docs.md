# Developer documentation

This documentation is for developers of Baker. test

## Creating a release

To create a release run the following:

1. Make sure tests are OK:

    `sbt ";+clean;+test"`

2. Create the release:

    `sbt -mem 2048 "release cross skip-tests"`

    When prompted, enter the PGP password for signing the files.

## Documentation site at github.io

### Tools used

We use [mkdocs](https://github.com/mkdocs/mkdocs) with the [material](https://github.com/squidfunk/mkdocs-material) theme to generate the documentation site 

How to install the tools.

```
pip install --user mkdocs mkdocs-material pymdown-extensions
```

### Usage

Now you can serve the documentation using:

```
mkdocs serve
```

This will run an http server serving the site on port `8000`

All `.md` files are in de `/docs` directory.

If you add a file you must add it to the `/mkdocs.yml` file under `- nav: `.

### Publishing changes

When you have made changes you can publish the site on the `gh-pages` branch

```
mkdocs gh-deploy
```

This will automatically build, commit and push the site to the `gh-pages` branch on Github.

Afterwards you will need to update the ing-bank.github.io repository.

The `gh-pages` branch from baker is a sub repository located in the `/baker` directory.

If not cloned before, clone from https://github.com/ing-bank/ing-bank.github.io with the following command:
``` bash
git clone --recurse-submodules https://github.com/ing-bank/ing-bank.github.io.git
```

Then execute the following commands inside the repository directory.

``` bash
cd ing-bank.github.io/
git submodule update --recursive --remote
git commit -am 'update baker docs'
git push origin master
```
