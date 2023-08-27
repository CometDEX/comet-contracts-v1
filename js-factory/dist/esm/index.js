import { xdr } from 'soroban-client';
import { Buffer } from "buffer";
import { scValStrToJs, scValToJs, addressToScVal, strToScVal } from './convert.js';
import { invoke } from './invoke.js';
export * from './constants.js';
export * from './server.js';
export * from './invoke.js';
;
;
export class Ok {
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
export class Err {
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
if (typeof window !== 'undefined') {
    //@ts-ignore Buffer exists
    window.Buffer = window.Buffer || Buffer;
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
        return xdr.ScVal.scvVoid();
    }
    let res = [];
    switch (dataKeyFactory.tag) {
        case "IsCpool":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("IsCpool"));
            res.push(((i) => addressToScVal(i))(dataKeyFactory.values[0]));
            break;
        case "Admin":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("Admin"));
            break;
        case "WasmHash":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("WasmHash"));
            break;
    }
    return xdr.ScVal.scvVec(res);
}
function DataKeyFactoryFromXdr(base64Xdr) {
    let [tag, values] = strToScVal(base64Xdr).vec().map(scValToJs);
    if (!tag) {
        throw new Error('Missing enum tag when decoding DataKeyFactory from XDR');
    }
    return { tag, values };
}
function NewPoolEventToXdr(newPoolEvent) {
    if (!newPoolEvent) {
        return xdr.ScVal.scvVoid();
    }
    let arr = [
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("caller"), val: ((i) => addressToScVal(i))(newPoolEvent["caller"]) }),
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("pool"), val: ((i) => addressToScVal(i))(newPoolEvent["pool"]) })
    ];
    return xdr.ScVal.scvMap(arr);
}
function NewPoolEventFromXdr(base64Xdr) {
    let scVal = strToScVal(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        caller: scValToJs(map.get("caller")),
        pool: scValToJs(map.get("pool"))
    };
}
function SetAdminEventToXdr(setAdminEvent) {
    if (!setAdminEvent) {
        return xdr.ScVal.scvVoid();
    }
    let arr = [
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("admin"), val: ((i) => addressToScVal(i))(setAdminEvent["admin"]) }),
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("caller"), val: ((i) => addressToScVal(i))(setAdminEvent["caller"]) })
    ];
    return xdr.ScVal.scvMap(arr);
}
function SetAdminEventFromXdr(base64Xdr) {
    let scVal = strToScVal(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        admin: scValToJs(map.get("admin")),
        caller: scValToJs(map.get("caller"))
    };
}
export async function init({ user, pool_wasm_hash }, options = {}) {
    return await invoke({
        method: 'init',
        args: [((i) => addressToScVal(i))(user),
            ((i) => xdr.ScVal.scvBytes(i))(pool_wasm_hash)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function newCPool({ salt, user }, options = {}) {
    return await invoke({
        method: 'new_c_pool',
        args: [((i) => xdr.ScVal.scvBytes(i))(salt),
            ((i) => addressToScVal(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function setCAdmin({ caller, user }, options = {}) {
    return await invoke({
        method: 'set_c_admin',
        args: [((i) => addressToScVal(i))(caller),
            ((i) => addressToScVal(i))(user)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function getCAdmin(options = {}) {
    return await invoke({
        method: 'get_c_admin',
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function isCPool({ addr }, options = {}) {
    return await invoke({
        method: 'is_c_pool',
        args: [((i) => addressToScVal(i))(addr)],
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function collect({ caller, addr }, options = {}) {
    return await invoke({
        method: 'collect',
        args: [((i) => addressToScVal(i))(caller),
            ((i) => addressToScVal(i))(addr)],
        ...options,
        parseResultXdr: () => { },
    });
}
