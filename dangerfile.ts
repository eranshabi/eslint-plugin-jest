'use strict';

// shamelessly "borrowed" from https://github.com/danger/danger-js/blob/master/source/danger.d.ts b/c we danger via npx
// eslint-disable-next-line no-var
declare var danger: {
  github: {
    pr: {
      body: string;
    };
  };
  git: {
    created_files: string[];
    modified_files: string[];
  };
};

// Ensure that people include a description on their PRs
if (danger.github.pr.body.length === 0) {
  fail('Please include a body for your PR');
}

if (
  danger.git.created_files.find(filename => filename.startsWith('rules/')) &&
  !danger.git.modified_files.includes('README.md')
) {
  fail('Please update the README when new rules are added');
}
