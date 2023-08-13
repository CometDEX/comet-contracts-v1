"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.symbol = exports.name = exports.decimals = exports.setAdmin = exports.mint = exports.setAuthorized = exports.clawback = exports.burnFrom = exports.burn = exports.transferFrom = exports.transfer = exports.authorized = exports.spendableBalance = exports.balance = exports.approve = exports.allowance = exports.initialize = exports.Err = exports.Ok = void 0;
const soroban_client_1 = require("soroban-client");
const buffer_1 = require("buffer");
const convert_js_1 = require("./convert.js");
const invoke_js_1 = require("./invoke.js");
__exportStar(require("./constants.js"), exports);
__exportStar(require("./server.js"), exports);
__exportStar(require("./invoke.js"), exports);
;
;
class Ok {
    value;
    constructor(value) {
        this.value = value;
    }
    unwrapErr() {
        throw new Error('No error');
    }
    unwrap() {
        return this.value;
    }
    isOk() {
        return true;
    }
    isErr() {
        return !this.isOk();
    }
}
exports.Ok = Ok;
class Err {
    error;
    constructor(error) {
        this.error = error;
    }
    unwrapErr() {
        return this.error;
    }
    unwrap() {
        throw new Error(this.error.message);
    }
    isOk() {
        return false;
    }
    isErr() {
        return !this.isOk();
    }
}
exports.Err = Err;
if (typeof window !== 'undefined') {
    //@ts-ignore Buffer exists
    window.Buffer = window.Buffer || buffer_1.Buffer;
}
const regex = /ContractError\((\d+)\)/;
function getError(err) {
    const match = err.match(regex);
    if (!match) {
        return undefined;
    }
    if (Errors == undefined) {
        return undefined;
    }
    // @ts-ignore
    let i = parseInt(match[1], 10);
    if (i < Errors.length) {
        return new Err(Errors[i]);
    }
    return undefined;
}
async function initialize({ admin, decimal, name, symbol }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'initialize',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(admin),
            ((i) => soroban_client_1.xdr.ScVal.scvU32(i))(decimal),
            ((i) => soroban_client_1.xdr.ScVal.scvString(i))(name),
            ((i) => soroban_client_1.xdr.ScVal.scvString(i))(symbol)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.initialize = initialize;
async function allowance({ from, spender }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'allowance',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(spender)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.allowance = allowance;
async function approve({ from, spender, amount, expiration_ledger }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'approve',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(spender),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount),
            ((i) => soroban_client_1.xdr.ScVal.scvU32(i))(expiration_ledger)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.approve = approve;
async function balance({ id }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'balance',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(id)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.balance = balance;
async function spendableBalance({ id }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'spendable_balance',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(id)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.spendableBalance = spendableBalance;
async function authorized({ id }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'authorized',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(id)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.authorized = authorized;
async function transfer({ from, to, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'transfer',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(to),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.transfer = transfer;
async function transferFrom({ spender, from, to, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'transfer_from',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(spender),
            ((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(to),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.transferFrom = transferFrom;
async function burn({ from, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'burn',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.burn = burn;
async function burnFrom({ spender, from, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'burn_from',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(spender),
            ((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.burnFrom = burnFrom;
async function clawback({ from, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'clawback',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.clawback = clawback;
async function setAuthorized({ id, authorize }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_authorized',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(id),
            ((i) => soroban_client_1.xdr.ScVal.scvBool(i))(authorize)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setAuthorized = setAuthorized;
async function mint({ to, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'mint',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(to),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.mint = mint;
async function setAdmin({ new_admin }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_admin',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(new_admin)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setAdmin = setAdmin;
async function decimals(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'decimals',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.decimals = decimals;
async function name(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'name',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.name = name;
async function symbol(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'symbol',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.symbol = symbol;
function AllowanceDataKeyToXdr(allowanceDataKey) {
    if (!allowanceDataKey) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("from"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(allowanceDataKey["from"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("spender"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(allowanceDataKey["spender"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function AllowanceDataKeyFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        from: (0, convert_js_1.scValToJs)(map.get("from")),
        spender: (0, convert_js_1.scValToJs)(map.get("spender"))
    };
}
function AllowanceValueToXdr(allowanceValue) {
    if (!allowanceValue) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("amount"), val: ((i) => (0, convert_js_1.i128ToScVal)(i))(allowanceValue["amount"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("expiration_ledger"), val: ((i) => soroban_client_1.xdr.ScVal.scvU32(i))(allowanceValue["expiration_ledger"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function AllowanceValueFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        amount: (0, convert_js_1.scValToJs)(map.get("amount")),
        expiration_ledger: (0, convert_js_1.scValToJs)(map.get("expiration_ledger"))
    };
}
function DataKeyToXdr(dataKey) {
    if (!dataKey) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let res = [];
    switch (dataKey.tag) {
        case "Allowance":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Allowance"));
            res.push(((i) => AllowanceDataKeyToXdr(i))(dataKey.values[0]));
            break;
        case "Balance":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Balance"));
            res.push(((i) => (0, convert_js_1.addressToScVal)(i))(dataKey.values[0]));
            break;
        case "Nonce":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Nonce"));
            res.push(((i) => (0, convert_js_1.addressToScVal)(i))(dataKey.values[0]));
            break;
        case "State":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("State"));
            res.push(((i) => (0, convert_js_1.addressToScVal)(i))(dataKey.values[0]));
            break;
        case "Admin":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Admin"));
            break;
    }
    return soroban_client_1.xdr.ScVal.scvVec(res);
}
function DataKeyFromXdr(base64Xdr) {
    let [tag, values] = (0, convert_js_1.strToScVal)(base64Xdr).vec().map(convert_js_1.scValToJs);
    if (!tag) {
        throw new Error('Missing enum tag when decoding DataKey from XDR');
    }
    return { tag, values };
}
function TokenMetadataToXdr(tokenMetadata) {
    if (!tokenMetadata) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("decimal"), val: ((i) => soroban_client_1.xdr.ScVal.scvU32(i))(tokenMetadata["decimal"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("name"), val: ((i) => soroban_client_1.xdr.ScVal.scvString(i))(tokenMetadata["name"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("symbol"), val: ((i) => soroban_client_1.xdr.ScVal.scvString(i))(tokenMetadata["symbol"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function TokenMetadataFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        decimal: (0, convert_js_1.scValToJs)(map.get("decimal")),
        name: (0, convert_js_1.scValToJs)(map.get("name")),
        symbol: (0, convert_js_1.scValToJs)(map.get("symbol"))
    };
}
const Errors = [];
