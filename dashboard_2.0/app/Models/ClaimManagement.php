<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class ClaimManagement extends Model
{
    protected $table = "claim_management";
    protected $fillable = [
        "claim_id",
        "intimationDate",
        "claimNumber",
        "surveyorName",
        "surveyorMobileNo",
        "surveyorEmail",
        "surveyorDeputationDateTime",
        "surveyorDate",
        "surveyorTime",
        "workDateTime",
        "workEstimatedAmount",
        "workClaimApprovalAmount",
        "deliveryClaimType",
        "deliveryInvoiceAmount",
        "deliveryClaimApprovalAmount",
        "deliveryDifferenceAmount",
        "deliveryCompulsoryDeductibles",
        "deliveryVoluntaryExcess",
        "deliveryDepreciation",
        "deliveryOthers",
        "settledPayeeName",
        "settledPaymentDate",
        "settledPaymentAmount",
        "settledReferenceNumber",
        "settledModeOfPayment",
        "rejectionReason",
        "withDrawAgree",
        "withDrawalReason",
        "claim_raised_status"
    ];

    protected $casts = [
        'withDrawAgree' => 'boolean',
    ];
}
