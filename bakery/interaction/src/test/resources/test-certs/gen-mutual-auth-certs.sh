export PW=changeit

rm *.jks

##
## Server related certs
##

# Create a self signed key pair root CA certificate.
keytool -genkeypair -v \
  -alias interactionca \
  -dname "CN=interactionca, OU=Bakery, O=Bakery, L=Amsterdam, ST=North Holland, C=Netherlands" \
  -keystore interactionca.jks \
  -keypass:env PW \
  -storepass:env PW \
  -keyalg RSA \
  -keysize 4096 \
  -ext KeyUsage:critical="keyCertSign" \
  -ext BasicConstraints:critical="ca:true" \
  -validity 9999

# Export the interactionca public certificate as interactionca.crt so that it can be used in trust stores.
keytool -export -v \
  -alias interactionca \
  -file interactionca.crt \
  -keypass:env PW \
  -storepass:env PW \
  -keystore interactionca.jks \
  -rfc

# Create a server certificate, tied to interaction.ing-bank.github.io
keytool -genkeypair -v \
  -alias interaction.ing-bank.github.io \
  -dname "CN=interaction.ing-bank.github.io, OU=Bakery, O=Bakery, L=Amsterdam, ST=North Holland, C=Netherlands" \
  -keystore interaction.ing-bank.github.io.jks \
  -keypass:env PW \
  -storepass:env PW \
  -keyalg RSA \
  -keysize 2048 \
  -validity 9999

# Create a certificate signing request for interaction.ing-bank.github.io
keytool -certreq -v \
  -alias interaction.ing-bank.github.io \
  -keypass:env PW \
  -storepass:env PW \
  -keystore interaction.ing-bank.github.io.jks \
  -file interaction.ing-bank.github.io.csr

# Tell interactionca to sign the interaction.ing-bank.github.io certificate. Note the extension is on the request, not the
# original certificate.
# Technically, keyUsage should be digitalSignature for DHE or ECDHE, keyEncipherment for RSA.
keytool -gencert -v \
  -alias interactionca \
  -keypass:env PW \
  -storepass:env PW \
  -keystore interactionca.jks \
  -infile interaction.ing-bank.github.io.csr \
  -outfile interaction.ing-bank.github.io.crt \
  -ext KeyUsage:critical="digitalSignature,keyEncipherment" \
  -ext EKU="serverAuth" \
  -ext SAN="dns:localhost,ip:127.0.0.1,ip:::1" \
  -rfc

# Tell interaction.ing-bank.github.io.jks it can trust interactionca as a signer.
keytool -import -v \
  -alias interactionca \
  -file interactionca.crt \
  -keystore interaction.ing-bank.github.io.jks \
  -storetype JKS \
  -storepass:env PW << EOF
yes
EOF

# Import the signed certificate back into interaction.ing-bank.github.io.jks
keytool -import -v \
  -alias interaction.ing-bank.github.io \
  -file interaction.ing-bank.github.io.crt \
  -keystore interaction.ing-bank.github.io.jks \
  -storetype JKS \
  -storepass:env PW

##
## Client related certs
##

# Create a self signed certificate & private key to create a root certificate authority.
keytool -genkeypair -v \
  -alias interactionclientca \
  -dname "CN=interactionclientca, OU=Bakery, O=Bakery, L=Amsterdam, ST=North Holland, C=Netherlands" \
  -keystore client.interaction.ing-bank.github.io.jks \
  -keypass:env PW \
  -storepass:env PW \
  -keyalg RSA \
  -keysize 4096 \
  -ext KeyUsage:critical="keyCertSign" \
  -ext BasicConstraints:critical="ca:true" \
  -validity 9999

# Create key pair that will act as the client.
keytool -genkeypair -v \
  -alias client.interaction.ing-bank.github.io \
  -keystore client.interaction.ing-bank.github.io.jks \
  -dname "CN=client.interaction.ing-bank.github.io, OU=Bakery, O=Bakery, L=Amsterdam, ST=North Holland, C=Netherlands" \
  -keypass:env PW \
  -storepass:env PW \
  -keyalg RSA \
  -keysize 2048 \
  -validity 9999

# Create a certificate signing request from the client.interaction.ing-bank.github.io certificate.
keytool -certreq -v \
  -alias client.interaction.ing-bank.github.io \
  -keypass:env PW \
  -storepass:env PW \
  -keystore client.interaction.ing-bank.github.io.jks \
  -file client.interaction.ing-bank.github.io.csr

# Make interactionclientca create a certificate chain saying that client.interaction.ing-bank.github.io is signed by interactionclientca.
keytool -gencert -v \
  -alias interactionclientca \
  -keypass:env PW \
  -storepass:env PW \
  -keystore client.interaction.ing-bank.github.io.jks \
  -infile client.interaction.ing-bank.github.io.csr \
  -outfile client.interaction.ing-bank.github.io.crt \
  -ext EKU="clientAuth" \
  -rfc

# Export the interactionclientca certificate from the keystore.  This goes on the http server
# and is presented in the CertificateRequest.
keytool -export -v \
  -alias interactionclientca \
  -file interactionclientca.crt \
  -storepass:env PW \
  -keystore client.interaction.ing-bank.github.io.jks \
  -rfc

# Import the signed certificate back into client.interaction.ing-bank.github.io.jks.  This is important, as JSSE won't send a client.interaction.ing-bank.github.io
# certificate if it can't find one signed by the client.interaction.ing-bank.github.io-ca presented in the CertificateRequest.
keytool -import -v \
  -alias client.interaction.ing-bank.github.io \
  -file client.interaction.ing-bank.github.io.crt \
  -keystore client.interaction.ing-bank.github.io.jks \
  -storetype JKS \
  -storepass:env PW

# Export the interactionclientca's certificate and private key to pkcs12, so it's safe.
#keytool -importkeystore -v \
#  -srcalias interactionclientca \
#  -srckeystore client.interaction.ing-bank.github.io.jks \
#  -srcstorepass:env PW \
#  -destkeystore interactionclientca.p12 \
#  -deststorepass:env PW \
#  -deststoretype PKCS12

# Import the interactionclientca's public certificate into a JKS store for Play Server to read.  We don't use
# the PKCS12 because it's got the CA private key and we don't want that.
keytool -import -v \
  -alias interactionclientca \
  -file interactionclientca.crt \
  -keystore interactionclientca.jks \
  -storepass:env PW << EOF
yes
EOF

# Then, strip out the interactionclientca alias from client.interaction.ing-bank.github.io.jks, just leaving the signed certificate.
keytool -delete -v \
 -alias interactionclientca \
 -storepass:env PW \
 -keystore client.interaction.ing-bank.github.io.jks

##
## Mutual trust
##

# Make client trust the server ca
keytool -import \
  -alias interactionca \
  -file interactionca.crt \
  -keystore client.interaction.ing-bank.github.io.jks \
  -storetype JKS \
  -storepass:env PW << EOF
yes
EOF

cp interaction.ing-bank.github.io.jks interaction.ing-bank.github.io_NO_CLIENT_TRUST.jks

# Make server trust the client ca
keytool -import \
  -alias interactionclientca \
  -file interactionclientca.crt \
  -keystore interaction.ing-bank.github.io.jks \
  -storepass:env PW << EOF
yes
EOF

rm *.crt && rm *.csr && rm interactionca.jks && rm interactionclientca.jks
