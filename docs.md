# Developer documentation

This documentation is for developers of Baker.

## Creating a release

CI and release processes are fully automated using the following Github Action workflows:

* [CI workflow](https://github.com/ing-bank/baker/blob/master/.github/workflows/ci.yml): Runs for each commit to any branch and also for release tags starting with 'v'. This workflow runs all tests, updates the draft release notes, uploads dependency graph to github (only for master branch) and publishes to Sonatype/Maven or Azure depending on following conditions.
    
    * Sonatype/Maven: Only for tags starting with 'v' prefix.

    * Azure: All commits to all branches except the tagged commits, so we have stable releases in Sonatype and non-stable more frequent releases in Azure for ING internal use and tests.

* [Release workflow](https://github.com/ing-bank/baker/blob/master/.github/workflows/release.yml): Manually triggered by one of the contributors when a stable release to Sonatype Maven Central is needed. This workflow just creates and pushes a tag. Then CI workflow gets triggered by the tag (i.e v1.0.0) and artifacts published to Sonatype Maven Central with the version in the tag.

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
