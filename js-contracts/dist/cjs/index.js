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
exports.setAuth = exports.clawback = exports.burnFrom = exports.burn = exports.xferFrom = exports.xfer = exports.authorized = exports.spendable = exports.balance = exports.decrAllow = exports.incrAllow = exports.allowance = exports.initialize = exports.isBound = exports.isFinalized = exports.isPublicSwap = exports.shareId = exports.getSpotPriceSansFee = exports.getSwapFee = exports.getSpotPrice = exports.getNormalizedWeight = exports.getDenormalizedWeight = exports.getBalance = exports.getFinalTokens = exports.getCurrentTokens = exports.getNumTokens = exports.getTotalDenormalizedWeight = exports.getController = exports.getTotalSupply = exports.setFreezeStatus = exports.setPublicSwap = exports.setController = exports.setSwapFee = exports.wdrToknAmtOutGetLpToknsIn = exports.wdrToknAmtInGetLpToknsOut = exports.depLpToknAmtOutGetToknIn = exports.depToknAmtInGetLpToknsOut = exports.swapExactAmountOut = exports.swapExactAmountIn = exports.exitPool = exports.joinPool = exports.gulp = exports.finalize = exports.unbind = exports.rebind = exports.bind = exports.bundleBind = exports.init = exports.Err = exports.Ok = void 0;
exports.symbol = exports.name = exports.decimals = exports.setAdmin = exports.mint = void 0;
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
async function init({ factory, controller }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'init',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(factory),
            ((i) => (0, convert_js_1.addressToScVal)(i))(controller)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.init = init;
async function bundleBind({ token, balance, denorm }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'bundle_bind',
        args: [((i) => soroban_client_1.xdr.ScVal.scvVec(i.map((i) => (0, convert_js_1.addressToScVal)(i))))(token),
            ((i) => soroban_client_1.xdr.ScVal.scvVec(i.map((i) => (0, convert_js_1.i128ToScVal)(i))))(balance),
            ((i) => soroban_client_1.xdr.ScVal.scvVec(i.map((i) => (0, convert_js_1.i128ToScVal)(i))))(denorm)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.bundleBind = bundleBind;
async function bind({ token, balance, denorm, admin }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'bind',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(balance),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(denorm),
            ((i) => (0, convert_js_1.addressToScVal)(i))(admin)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.bind = bind;
async function rebind({ token, balance, denorm, admin }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'rebind',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(balance),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(denorm),
            ((i) => (0, convert_js_1.addressToScVal)(i))(admin)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.rebind = rebind;
async function unbind({ token, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'unbind',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.unbind = unbind;
async function finalize(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'finalize',
        ...options,
        parseResultXdr: () => { },
    });
}
exports.finalize = finalize;
async function gulp({ t }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'gulp',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(t)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.gulp = gulp;
async function joinPool({ pool_amount_out, max_amounts_in, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'join_pool',
        args: [((i) => (0, convert_js_1.i128ToScVal)(i))(pool_amount_out),
            ((i) => soroban_client_1.xdr.ScVal.scvVec(i.map((i) => (0, convert_js_1.i128ToScVal)(i))))(max_amounts_in),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.joinPool = joinPool;
async function exitPool({ pool_amount_in, min_amounts_out, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'exit_pool',
        args: [((i) => (0, convert_js_1.i128ToScVal)(i))(pool_amount_in),
            ((i) => soroban_client_1.xdr.ScVal.scvVec(i.map((i) => (0, convert_js_1.i128ToScVal)(i))))(min_amounts_out),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.exitPool = exitPool;
async function swapExactAmountIn({ token_in, token_amount_in, token_out, min_amount_out, max_price, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'swap_exact_amount_in',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_in),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(token_amount_in),
            ((i) => (0, convert_js_1.addressToScVal)(i))(token_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(min_amount_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(max_price),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.swapExactAmountIn = swapExactAmountIn;
async function swapExactAmountOut({ token_in, max_amount_in, token_out, token_amount_out, max_price, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'swap_exact_amount_out',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_in),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(max_amount_in),
            ((i) => (0, convert_js_1.addressToScVal)(i))(token_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(token_amount_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(max_price),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.swapExactAmountOut = swapExactAmountOut;
async function depToknAmtInGetLpToknsOut({ token_in, token_amount_in, min_pool_amount_out, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'dep_tokn_amt_in_get_lp_tokns_out',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_in),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(token_amount_in),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(min_pool_amount_out),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.depToknAmtInGetLpToknsOut = depToknAmtInGetLpToknsOut;
async function depLpToknAmtOutGetToknIn({ token_in, pool_amount_out, max_amount_in, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'dep_lp_tokn_amt_out_get_tokn_in',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_in),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(pool_amount_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(max_amount_in),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.depLpToknAmtOutGetToknIn = depLpToknAmtOutGetToknIn;
async function wdrToknAmtInGetLpToknsOut({ token_out, pool_amount_in, min_amount_out, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'wdr_tokn_amt_in_get_lp_tokns_out',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(pool_amount_in),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(min_amount_out),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.wdrToknAmtInGetLpToknsOut = wdrToknAmtInGetLpToknsOut;
async function wdrToknAmtOutGetLpToknsIn({ token_out, token_amount_out, max_pool_amount_in, user }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'wdr_tokn_amt_out_get_lp_tokns_in',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(token_amount_out),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(max_pool_amount_in),
            ((i) => (0, convert_js_1.addressToScVal)(i))(user)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.wdrToknAmtOutGetLpToknsIn = wdrToknAmtOutGetLpToknsIn;
async function setSwapFee({ fee, caller }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_swap_fee',
        args: [((i) => (0, convert_js_1.i128ToScVal)(i))(fee),
            ((i) => (0, convert_js_1.addressToScVal)(i))(caller)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setSwapFee = setSwapFee;
async function setController({ caller, manager }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_controller',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(caller),
            ((i) => (0, convert_js_1.addressToScVal)(i))(manager)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setController = setController;
async function setPublicSwap({ caller, val }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_public_swap',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(caller),
            ((i) => soroban_client_1.xdr.ScVal.scvBool(i))(val)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setPublicSwap = setPublicSwap;
async function setFreezeStatus({ caller, val }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_freeze_status',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(caller),
            ((i) => soroban_client_1.xdr.ScVal.scvBool(i))(val)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setFreezeStatus = setFreezeStatus;
async function getTotalSupply(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_total_supply',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getTotalSupply = getTotalSupply;
async function getController(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_controller',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getController = getController;
async function getTotalDenormalizedWeight(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_total_denormalized_weight',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getTotalDenormalizedWeight = getTotalDenormalizedWeight;
async function getNumTokens(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_num_tokens',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getNumTokens = getNumTokens;
async function getCurrentTokens(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_current_tokens',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getCurrentTokens = getCurrentTokens;
async function getFinalTokens(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_final_tokens',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getFinalTokens = getFinalTokens;
async function getBalance({ token }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_balance',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getBalance = getBalance;
async function getDenormalizedWeight({ token }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_denormalized_weight',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getDenormalizedWeight = getDenormalizedWeight;
async function getNormalizedWeight({ token }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_normalized_weight',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getNormalizedWeight = getNormalizedWeight;
async function getSpotPrice({ token_in, token_out }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_spot_price',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_in),
            ((i) => (0, convert_js_1.addressToScVal)(i))(token_out)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getSpotPrice = getSpotPrice;
async function getSwapFee(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_swap_fee',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getSwapFee = getSwapFee;
async function getSpotPriceSansFee({ token_in, token_out }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'get_spot_price_sans_fee',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(token_in),
            ((i) => (0, convert_js_1.addressToScVal)(i))(token_out)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.getSpotPriceSansFee = getSpotPriceSansFee;
async function shareId(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'share_id',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.shareId = shareId;
async function isPublicSwap(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'is_public_swap',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.isPublicSwap = isPublicSwap;
async function isFinalized(options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'is_finalized',
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.isFinalized = isFinalized;
async function isBound({ t }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'is_bound',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(t)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.isBound = isBound;
async function initialize({ admin, decimal, name, symbol }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'initialize',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(admin),
            ((i) => soroban_client_1.xdr.ScVal.scvU32(i))(decimal),
            ((i) => soroban_client_1.xdr.ScVal.scvBytes(i))(name),
            ((i) => soroban_client_1.xdr.ScVal.scvBytes(i))(symbol)],
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
async function incrAllow({ from, spender, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'incr_allow',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(spender),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.incrAllow = incrAllow;
async function decrAllow({ from, spender, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'decr_allow',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(spender),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.decrAllow = decrAllow;
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
async function spendable({ id }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'spendable',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(id)],
        ...options,
        parseResultXdr: (xdr) => {
            return (0, convert_js_1.scValStrToJs)(xdr);
        },
    });
}
exports.spendable = spendable;
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
async function xfer({ from, to, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'xfer',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(to),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.xfer = xfer;
async function xferFrom({ spender, from, to, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'xfer_from',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(spender),
            ((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.addressToScVal)(i))(to),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.xferFrom = xferFrom;
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
async function clawback({ admin, from, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'clawback',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(admin),
            ((i) => (0, convert_js_1.addressToScVal)(i))(from),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.clawback = clawback;
async function setAuth({ admin, id, authorize }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_auth',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(admin),
            ((i) => (0, convert_js_1.addressToScVal)(i))(id),
            ((i) => soroban_client_1.xdr.ScVal.scvBool(i))(authorize)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.setAuth = setAuth;
async function mint({ admin, to, amount }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'mint',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(admin),
            ((i) => (0, convert_js_1.addressToScVal)(i))(to),
            ((i) => (0, convert_js_1.i128ToScVal)(i))(amount)],
        ...options,
        parseResultXdr: () => { },
    });
}
exports.mint = mint;
async function setAdmin({ admin, new_admin }, options = {}) {
    return await (0, invoke_js_1.invoke)({
        method: 'set_admin',
        args: [((i) => (0, convert_js_1.addressToScVal)(i))(admin),
            ((i) => (0, convert_js_1.addressToScVal)(i))(new_admin)],
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
function SwapEventToXdr(swapEvent) {
    if (!swapEvent) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("caller"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(swapEvent["caller"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_amount_in"), val: ((i) => (0, convert_js_1.i128ToScVal)(i))(swapEvent["token_amount_in"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_amount_out"), val: ((i) => (0, convert_js_1.i128ToScVal)(i))(swapEvent["token_amount_out"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_in"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(swapEvent["token_in"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_out"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(swapEvent["token_out"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function SwapEventFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        caller: (0, convert_js_1.scValToJs)(map.get("caller")),
        token_amount_in: (0, convert_js_1.scValToJs)(map.get("token_amount_in")),
        token_amount_out: (0, convert_js_1.scValToJs)(map.get("token_amount_out")),
        token_in: (0, convert_js_1.scValToJs)(map.get("token_in")),
        token_out: (0, convert_js_1.scValToJs)(map.get("token_out"))
    };
}
function JoinEventToXdr(joinEvent) {
    if (!joinEvent) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("caller"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(joinEvent["caller"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_amount_in"), val: ((i) => (0, convert_js_1.i128ToScVal)(i))(joinEvent["token_amount_in"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_in"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(joinEvent["token_in"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function JoinEventFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        caller: (0, convert_js_1.scValToJs)(map.get("caller")),
        token_amount_in: (0, convert_js_1.scValToJs)(map.get("token_amount_in")),
        token_in: (0, convert_js_1.scValToJs)(map.get("token_in"))
    };
}
function ExitEventToXdr(exitEvent) {
    if (!exitEvent) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("caller"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(exitEvent["caller"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_amount_out"), val: ((i) => (0, convert_js_1.i128ToScVal)(i))(exitEvent["token_amount_out"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("token_out"), val: ((i) => (0, convert_js_1.addressToScVal)(i))(exitEvent["token_out"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function ExitEventFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        caller: (0, convert_js_1.scValToJs)(map.get("caller")),
        token_amount_out: (0, convert_js_1.scValToJs)(map.get("token_amount_out")),
        token_out: (0, convert_js_1.scValToJs)(map.get("token_out"))
    };
}
function RecordToXdr(record) {
    if (!record) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let arr = [
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("balance"), val: ((i) => (0, convert_js_1.i128ToScVal)(i))(record["balance"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("bound"), val: ((i) => soroban_client_1.xdr.ScVal.scvBool(i))(record["bound"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("denorm"), val: ((i) => (0, convert_js_1.i128ToScVal)(i))(record["denorm"]) }),
        new soroban_client_1.xdr.ScMapEntry({ key: ((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("index"), val: ((i) => soroban_client_1.xdr.ScVal.scvU32(i))(record["index"]) })
    ];
    return soroban_client_1.xdr.ScVal.scvMap(arr);
}
function RecordFromXdr(base64Xdr) {
    let scVal = (0, convert_js_1.strToScVal)(base64Xdr);
    let obj = scVal.map().map(e => [e.key().str(), e.val()]);
    let map = new Map(obj);
    if (!obj) {
        throw new Error('Invalid XDR');
    }
    return {
        balance: (0, convert_js_1.scValToJs)(map.get("balance")),
        bound: (0, convert_js_1.scValToJs)(map.get("bound")),
        denorm: (0, convert_js_1.scValToJs)(map.get("denorm")),
        index: (0, convert_js_1.scValToJs)(map.get("index"))
    };
}
function DataKeyToXdr(dataKey) {
    if (!dataKey) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let res = [];
    switch (dataKey.tag) {
        case "Factory":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Factory"));
            break;
        case "Controller":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Controller"));
            break;
        case "SwapFee":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("SwapFee"));
            break;
        case "TotalWeight":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("TotalWeight"));
            break;
        case "AllTokenVec":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("AllTokenVec"));
            break;
        case "AllRecordData":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("AllRecordData"));
            break;
        case "TokenShare":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("TokenShare"));
            break;
        case "TotalShares":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("TotalShares"));
            break;
        case "PublicSwap":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("PublicSwap"));
            break;
        case "Finalize":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Finalize"));
            break;
        case "Freeze":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Freeze"));
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
function DataKeyTokenToXdr(dataKeyToken) {
    if (!dataKeyToken) {
        return soroban_client_1.xdr.ScVal.scvVoid();
    }
    let res = [];
    switch (dataKeyToken.tag) {
        case "Allowance":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Allowance"));
            res.push(((i) => AllowanceDataKeyToXdr(i))(dataKeyToken.values[0]));
            break;
        case "Balance":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Balance"));
            res.push(((i) => (0, convert_js_1.addressToScVal)(i))(dataKeyToken.values[0]));
            break;
        case "Nonce":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Nonce"));
            res.push(((i) => (0, convert_js_1.addressToScVal)(i))(dataKeyToken.values[0]));
            break;
        case "State":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("State"));
            res.push(((i) => (0, convert_js_1.addressToScVal)(i))(dataKeyToken.values[0]));
            break;
        case "Admin":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Admin"));
            break;
        case "Decimals":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Decimals"));
            break;
        case "Name":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Name"));
            break;
        case "Symbol":
            res.push(((i) => soroban_client_1.xdr.ScVal.scvSymbol(i))("Symbol"));
            break;
    }
    return soroban_client_1.xdr.ScVal.scvVec(res);
}
function DataKeyTokenFromXdr(base64Xdr) {
    let [tag, values] = (0, convert_js_1.strToScVal)(base64Xdr).vec().map(convert_js_1.scValToJs);
    if (!tag) {
        throw new Error('Missing enum tag when decoding DataKeyToken from XDR');
    }
    return { tag, values };
}
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
const Errors = [
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" },
    { message: "" }
];
