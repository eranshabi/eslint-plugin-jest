'use strict';

// todo: https://github.com/babel/babel/issues/8529 :'(
module.exports = {
  presets: [
    '@babel/preset-typescript',
    ['@babel/preset-env', { targets: { node: 6 } }],
  ],
};
