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
exports.collect = exports.isCPool = exports.getCAdmin = exports.setCAdmin = exports.newCPool = exports.init = exports.Err = exports.Ok = void 0;
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
const Errors = [
    { message: "" },
    { message: "" },
    { message: "" }
];
function DataKeyFactoryToXdr(dataKeyFactory) {
    if (!dataKeyFactory) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let res = [];
    switch (dataKeyFactory.tag) {
        case "IsCpool":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("IsCpool"));
            res.push(((i) => (0, convert_js_1.addressToScVal)(i))(dataKeyFactory.values[0]));
            break;
        case "Admin":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Admin"));
            break;
        case "WasmHash":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("WasmHash"));
            break;
    }
    return soroban_client_1.xdr.ScVal.scvVec(res);
}
function DataKeyFactoryFromXdr(base64Xdr) {
    let [tag, values] = (0, convert_js_1.strToScVal)(base64Xdr).vec().map(convert_js_1.scValToJs);
    if (!tag) {
        throw new Error('Missing enum tag when decoding DataKeyFactory from XDR');
    }
    return { tag, values };
}
function NewPoolEventToXdr(newPoolEvent) {
    if (!newPoolEvent) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("caller"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(newPoolEvent["caller"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("pool"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(newPoolEvent["pool"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function NewPoolEventFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        caller: (0, convert_js_1.scValToJs)(map.get("caller")),
        pool: (0, convert_js_1.scValToJs)(map.get("pool"))
    };
}
function SetAdminEventToXdr(setAdminEvent) {
    if (!setAdminEvent) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("admin"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(setAdminEvent["admin"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("caller"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(setAdminEvent["caller"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function SetAdminEventFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        admin: (0, convert_js_1.scValToJs)(map.get("admin")),
        caller: (0, convert_js_1.scValToJs)(map.get("caller"))
    };
}
async function init({ user, pool_wasm_hash }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'init',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(user),
            ((i) => soroban_client_1.xdr.ScVal.scvBytes(i))(pool_wasm_hash)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.init = init;
async function newCPool({ salt, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'new_c_pool',
        args: [((i) => soroban_client_1.xdr.ScVal.scvBytes(i))(salt),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.newCPool = newCPool;
async function setCAdmin({ caller, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_c_admin',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(caller),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setCAdmin = setCAdmin;
async function getCAdmin(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_c_admin',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getCAdmin = getCAdmin;
async function isCPool({ addr }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'is_c_pool',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(addr)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.isCPool = isCPool;
async function collect({ caller, addr }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'collect',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(caller),
            ((i) => (0, convert_js_1.addressToScVal)(i))(addr)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.collect = collect;
