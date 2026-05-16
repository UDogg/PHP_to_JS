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
        Schema::create('au_branch_dump', function (Blueprint $table) {
            $table->bigIncrements('BranchID'); // Primary Key (AUTO_INCREMENT)
            $table->string('BranchCode', 50);
            $table->string('BranchName', 255);
            $table->string('Circle', 100)->nullable();
            $table->string('Zone', 100)->nullable();
            $table->string('Region', 100)->nullable();
            $table->string('Cluster', 100)->nullable();
            $table->string('State', 100)->nullable();
            $table->string('State_Wheels', 100)->nullable();
            $table->string('Hub_Wheels', 100)->nullable();
            $table->string('State_Agri_SME', 100)->nullable();
            $table->string('Hub_Agri_SME', 100)->nullable();
            $table->string('State_Home_Loans', 100)->nullable();
            $table->string('Hub_Home_Loans', 100)->nullable();
            $table->string('State_SBL_MSME', 100)->nullable();
            $table->string('Hub_SBL_MSME', 100)->nullable();
            $table->string('City', 150)->nullable();
            $table->string('Pincode', 10)->nullable();
            $table->string('Category_Urban_Core', 100)->nullable();
            $table->string('RBI_Classification', 100)->nullable();
            $table->string('Branch_Category3', 100)->nullable();
            $table->string('Branch_Launch_Date', 100)->nullable();
            $table->string('Branch_Type', 100)->nullable();
            $table->string('Tier', 50)->nullable();
            $table->text('Branch_Address')->nullable();
            $table->string('Reporting_Branch_Code', 50)->nullable();
            $table->string('Status', 255)->default('1');
            $table->decimal('Latitude', 10, 7)->nullable();
            $table->decimal('Longitude', 10, 7)->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('au_branch_dump');
    }
};
