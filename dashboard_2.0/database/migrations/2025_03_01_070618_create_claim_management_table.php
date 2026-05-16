<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::create('claim_management', function (Blueprint $table) {
            $table->id();
            $table->string('claim_id')->nullable();
            $table->string('intimationDate')->nullable();
            $table->string('claimNumber')->nullable();
            $table->string('surveyorName')->nullable();
            $table->string('surveyorMobileNo')->nullable();
            $table->string('surveyorEmail')->nullable();
            $table->string('surveyorDeputationDateTime')->nullable();
            $table->string('surveyorDate')->nullable();
            $table->string('surveyorTime')->nullable();
            $table->string('workDateTime')->nullable();
            $table->string('workEstimatedAmount')->nullable();
            $table->string('workClaimApprovalAmount')->nullable();
            $table->string('deliveryClaimType')->nullable();
            $table->string('deliveryInvoiceAmount')->nullable();
            $table->string('deliveryClaimApprovalAmount')->nullable();
            $table->string('deliveryDifferenceAmount')->nullable();
            $table->string('deliveryCompulsoryDeductibles')->nullable();
            $table->string('deliveryVoluntaryExcess')->nullable();
            $table->string('deliveryDepreciation')->nullable();
            $table->string('deliveryOthers')->nullable();
            $table->string('settledPayeeName')->nullable();
            $table->string('settledPaymentDate')->nullable();
            $table->string('settledPaymentAmount')->nullable();
            $table->string('settledReferenceNumber')->nullable();
            $table->string('settledModeOfPayment')->nullable();
            $table->string('rejectionReason')->nullable();
            $table->string('withDrawAgree')->nullable();
            $table->string('withDrawalReason')->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('claim_management');
    }
};
