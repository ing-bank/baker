ls -la $(pubring.secureFilePath)
ls -la $(secring.secureFilePath)

mkdir ~/.gnupg
chmod -R 700 ~/.gnupg
gpg --import  $(pubring.secureFilePath)
export GPG_TTY=$(tty)
gpg --batch --import $(secring.secureFilePath)
gpg --version
gpg --list-keys
gpg --list-secret-keys

git checkout oss-release
git config --global user.email "apollo@ing.com"
git config --global user.name "baker release pipeline"

export GPG_TTY=$(tty)
sbt -Divy.home=${IVY_HOME} -Dsbt.ivy.home=${IVY_HOME} "release with-defaults"
