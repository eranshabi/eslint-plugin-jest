import { RuleTester } from 'eslint';
import rule from '../prefer-to-be-undefined';

const ruleTester = new RuleTester();

ruleTester.run('prefer-to-be-undefined', rule, {
  valid: [
    'expect(undefined).toBeUndefined();',
    'expect(true).not.toBeUndefined();',
    'expect({}).toEqual({});',
    'expect(null).toEqual(null);',
    'expect(something).toBe(somethingElse)',
    'expect(something).toEqual(somethingElse)',
    'expect(something).not.toBe(somethingElse)',
    'expect(something).not.toEqual(somethingElse)',
    'expect(undefined).toBe',
    'expect("something");',
  ],

  invalid: [
    {
      code: 'expect(undefined).toBe(undefined);',
      errors: [{ messageId: 'useToBeUndefined', column: 19, line: 1 }],
      output: 'expect(undefined).toBeUndefined();',
    },
    {
      code: 'expect(undefined).toEqual(undefined);',
      errors: [{ messageId: 'useToBeUndefined', column: 19, line: 1 }],
      output: 'expect(undefined).toBeUndefined();',
    },
    {
      code: 'expect("a string").not.toBe(undefined);',
      errors: [{ messageId: 'useToBeUndefined', column: 24, line: 1 }],
      output: 'expect("a string").not.toBeUndefined();',
    },
    {
      code: 'expect("a string").not.toEqual(undefined);',
      errors: [{ messageId: 'useToBeUndefined', column: 24, line: 1 }],
      output: 'expect("a string").not.toBeUndefined();',
    },
  ],
});
