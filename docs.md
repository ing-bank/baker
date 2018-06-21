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

This will automatically build, commit and push the site to github.
