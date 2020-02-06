import React from 'react';
import { Admin, Resource } from 'react-admin';
import { UserList } from './Users'
import jsonServerProvider from 'ra-data-json-server';

const dataProvider = jsonServerProvider('http://jsonplaceholder.typicode.com');
const App = () => 
  <Admin dataProvider={dataProvider}>
    <Resource name="users" list={UserList}></Resource>
  </Admin>

export default App;