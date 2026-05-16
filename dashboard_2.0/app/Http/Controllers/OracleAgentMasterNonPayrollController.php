<?php

namespace App\Http\Controllers;

use App\Services\OracleAgentMasterNonPayrollService;
use Illuminate\Http\Request;

class OracleAgentMasterNonPayrollController extends Controller
{
    protected $service;

    public function __construct(OracleAgentMasterNonPayrollService $service)
    {
        $this->service = $service;
    }

    public function NonPayrollAgentMasterProcess()
    {
        return response()->json($this->service->processAgentMasterData());
    }
}
