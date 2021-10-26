#!/usr/bin/env bash
npm install @angular/cli
npm install
npx ng build --prod
#npm run test
#npm run lint
cd dist
zip -r ../dashboard.zip *
