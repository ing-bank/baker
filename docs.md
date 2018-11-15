## Tools used

We use [mkdocs](https://github.com/mkdocs/mkdocs) with the [material](https://github.com/squidfunk/mkdocs-material) theme to generate the documentation site 

See the links on how to install the tools.

For mac it is 2 commands:

```
brew install mkdocs
pip install --user mkdocs-material
```

## Howto

Now you can serve the documentation using:

```
mkdocs serve
```

This will run an http server serving the site on port `8000`

All `.md` files under docs are automatically added.

When you have made changes you can publish the site on the `gh-pages` branch

```
mkdocs gh-deploy
```

This will automatically build, commit and push the site to the `gh-pages` branch on Github.

Afterwards you will need to update the ing-bank.github.io repository.

The `gh-pages` branch from baker is a sub repository located in the `/baker` directory.

Pull (or clone) from https://github.com/ing-bank/ing-bank.github.io

Then execute the following commands inside the repository directory.

``` bash
git pull --recurse-submodules
git commit -am 'update baker docs'
git push
```
