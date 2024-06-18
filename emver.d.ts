/* tslint:disable */
/* eslint-disable */
/**
 * @param {string} version
 * @returns {string}
 */
export function flavor(version: string): string | null;
/**
 * @param {string} version
 * @returns {number}
 */
export function major(version: string): number;
/**
 * @param {string} version
 * @returns {number}
 */
export function minor(version: string): number;
/**
 * @param {string} version
 * @returns {number}
 */
export function patch(version: string): number;
/**
 * @param {string} version
 * @returns {number}
 */
export function revision(version: string): number;
/**
 * @param {string} version
 * @returns {string}
 */
export function prerelease(version: string): string | null;
/**
 * @param {string} lhs
 * @param {string} rhs
 * @returns {number | undefined}
 */
export function compare(lhs: string, rhs: string): number | null;
/**
 * @param {string} version
 * @param {string} range
 * @returns {boolean}
 */
export function satisfies(version: string, range: string): boolean;
