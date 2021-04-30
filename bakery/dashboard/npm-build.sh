#!/usr/bin/env bash
npm i
#npm run test
#npm run lint
npm run build --prod
cd dist
zip -r ../dashboard.zip *
