import { xdr } from 'soroban-client';
import { Buffer } from "buffer";
import { scValStrToJs, scValToJs, addressToScVal, i128ToScVal, strToScVal } from './convert.js';
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
export async function initialize({ admin, decimal, name, symbol }, options = {}) {
    return await invoke({
        method: 'initialize',
        args: [((i) => addressToScVal(i))(admin),
            ((i) => xdr.ScVal.scvU32(i))(decimal),
            ((i) => xdr.ScVal.scvString(i))(name),
            ((i) => xdr.ScVal.scvString(i))(symbol)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function allowance({ from, spender }, options = {}) {
    return await invoke({
        method: 'allowance',
        args: [((i) => addressToScVal(i))(from),
            ((i) => addressToScVal(i))(spender)],
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function approve({ from, spender, amount, expiration_ledger }, options = {}) {
    return await invoke({
        method: 'approve',
        args: [((i) => addressToScVal(i))(from),
            ((i) => addressToScVal(i))(spender),
            ((i) => i128ToScVal(i))(amount),
            ((i) => xdr.ScVal.scvU32(i))(expiration_ledger)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function balance({ id }, options = {}) {
    return await invoke({
        method: 'balance',
        args: [((i) => addressToScVal(i))(id)],
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function spendableBalance({ id }, options = {}) {
    return await invoke({
        method: 'spendable_balance',
        args: [((i) => addressToScVal(i))(id)],
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function authorized({ id }, options = {}) {
    return await invoke({
        method: 'authorized',
        args: [((i) => addressToScVal(i))(id)],
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function transfer({ from, to, amount }, options = {}) {
    return await invoke({
        method: 'transfer',
        args: [((i) => addressToScVal(i))(from),
            ((i) => addressToScVal(i))(to),
            ((i) => i128ToScVal(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function transferFrom({ spender, from, to, amount }, options = {}) {
    return await invoke({
        method: 'transfer_from',
        args: [((i) => addressToScVal(i))(spender),
            ((i) => addressToScVal(i))(from),
            ((i) => addressToScVal(i))(to),
            ((i) => i128ToScVal(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function burn({ from, amount }, options = {}) {
    return await invoke({
        method: 'burn',
        args: [((i) => addressToScVal(i))(from),
            ((i) => i128ToScVal(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function burnFrom({ spender, from, amount }, options = {}) {
    return await invoke({
        method: 'burn_from',
        args: [((i) => addressToScVal(i))(spender),
            ((i) => addressToScVal(i))(from),
            ((i) => i128ToScVal(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function clawback({ from, amount }, options = {}) {
    return await invoke({
        method: 'clawback',
        args: [((i) => addressToScVal(i))(from),
            ((i) => i128ToScVal(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function setAuthorized({ id, authorize }, options = {}) {
    return await invoke({
        method: 'set_authorized',
        args: [((i) => addressToScVal(i))(id),
            ((i) => xdr.ScVal.scvBool(i))(authorize)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function mint({ to, amount }, options = {}) {
    return await invoke({
        method: 'mint',
        args: [((i) => addressToScVal(i))(to),
            ((i) => i128ToScVal(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function setAdmin({ new_admin }, options = {}) {
    return await invoke({
        method: 'set_admin',
        args: [((i) => addressToScVal(i))(new_admin)],
        ...options,
        parseResultXdr: () => { },
    });
}
export async function decimals(options = {}) {
    return await invoke({
        method: 'decimals',
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function name(options = {}) {
    return await invoke({
        method: 'name',
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
export async function symbol(options = {}) {
    return await invoke({
        method: 'symbol',
        ...options,
        parseResultXdr: (xdr) => {
            return scValStrToJs(xdr);
        },
    });
}
function AllowanceDataKeyToXdr(allowanceDataKey) {
    if (!allowanceDataKey) {
        return xdr.ScVal.scvVoid();
    }
    let arr = [
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("from"), val: ((i) => addressToScVal(i))(allowanceDataKey["from"]) }),
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("spender"), val: ((i) => addressToScVal(i))(allowanceDataKey["spender"]) })
    ];
    return xdr.ScVal.scvMap(arr);
}
function AllowanceDataKeyFromXdr(base64Xdr) {
    let scVal = strToScVal(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        from: scValToJs(map.get("from")),
        spender: scValToJs(map.get("spender"))
    };
}
function AllowanceValueToXdr(allowanceValue) {
    if (!allowanceValue) {
        return xdr.ScVal.scvVoid();
    }
    let arr = [
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("amount"), val: ((i) => i128ToScVal(i))(allowanceValue["amount"]) }),
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("expiration_ledger"), val: ((i) => xdr.ScVal.scvU32(i))(allowanceValue["expiration_ledger"]) })
    ];
    return xdr.ScVal.scvMap(arr);
}
function AllowanceValueFromXdr(base64Xdr) {
    let scVal = strToScVal(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        amount: scValToJs(map.get("amount")),
        expiration_ledger: scValToJs(map.get("expiration_ledger"))
    };
}
function DataKeyToXdr(dataKey) {
    if (!dataKey) {
        return xdr.ScVal.scvVoid();
    }
    let res = [];
    switch (dataKey.tag) {
        case "Allowance":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("Allowance"));
            res.push(((i) => AllowanceDataKeyToXdr(i))(dataKey.values[0]));
            break;
        case "Balance":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("Balance"));
            res.push(((i) => addressToScVal(i))(dataKey.values[0]));
            break;
        case "Nonce":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("Nonce"));
            res.push(((i) => addressToScVal(i))(dataKey.values[0]));
            break;
        case "State":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("State"));
            res.push(((i) => addressToScVal(i))(dataKey.values[0]));
            break;
        case "Admin":
            res.push(((i) => xdr.ScVal.scvSymbol(i))("Admin"));
            break;
    }
    return xdr.ScVal.scvVec(res);
}
function DataKeyFromXdr(base64Xdr) {
    let [tag, values] = strToScVal(base64Xdr).vec().map(scValToJs);
    if (!tag) {
        throw new Error('Missing enum tag when decoding DataKey from XDR');
    }
    return { tag, values };
}
function TokenMetadataToXdr(tokenMetadata) {
    if (!tokenMetadata) {
        return xdr.ScVal.scvVoid();
    }
    let arr = [
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("decimal"), val: ((i) => xdr.ScVal.scvU32(i))(tokenMetadata["decimal"]) }),
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("name"), val: ((i) => xdr.ScVal.scvString(i))(tokenMetadata["name"]) }),
        new xdr.ScMapEntry({ key: ((i) => xdr.ScVal.scvSymbol(i))("symbol"), val: ((i) => xdr.ScVal.scvString(i))(tokenMetadata["symbol"]) })
    ];
    return xdr.ScVal.scvMap(arr);
}
function TokenMetadataFromXdr(base64Xdr) {
    let scVal = strToScVal(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        decimal: scValToJs(map.get("decimal")),
        name: scValToJs(map.get("name")),
        symbol: scValToJs(map.get("symbol"))
    };
}
const Errors = [];
