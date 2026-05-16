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
            $table->string('workShopName')->nullable();
            $table->string('lsoCode')->nullable();
            $table->string('workshopAddress')->nullable();
            $table->string('workshopEmail')->nullable();
            $table->string('workShopContact')->nullable();
            $table->string('workshopState')->nullable();
            $table->string('workshopCity')->nullable();
            $table->string('contactState')->nullable();
            $table->string('contactCity')->nullable();
            $table->string('contactPincode')->nullable();
            $table->string('driverName')->nullable();
            $table->string('insurerAddress')->nullable();
            $table->string('customerEmailId')->nullable();
            $table->string('customerMobileNo')->nullable();
            $table->string('mobileNo')->nullable();
            $table->string('intimatedName')->nullable();
            $table->string('claimIntimatedBy')->nullable();
            $table->string('descriptionOfAccident')->nullable();
            $table->string('catastrophicCode')->nullable();
            $table->string('partOfVehicle')->nullable();
            $table->string('dateOfAccident')->nullable();
            $table->string('placeOfAccident')->nullable();
            $table->string('accidentState')->nullable();
            $table->string('accidentCity')->nullable();
            $table->string('accidentCityPincode')->nullable();
            $table->string('natureOfAccident')->nullable();
            $table->string('option')->nullable();
            $table->string('wasVehicleParked')->nullable();
            $table->string('authorizedDealer')->nullable();
            $table->string('dealer')->nullable();
            $table->string('claim_status')->nullable();
            $table->string('claim_created_by')->nullable()->default(0);
            $table->string('reference_code')->nullable();
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
