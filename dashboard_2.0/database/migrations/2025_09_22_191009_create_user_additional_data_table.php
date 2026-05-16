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
        Schema::create('user_additional_data', function (Blueprint $table) {
            $table->id();
            $table->unsignedBigInteger('user_id');
            $table->foreign('user_id')->references('id')->on('users')->onDelete('cascade');
            $table->string('job_id')->nullable();
            $table->string('branch_code')->nullable();
            $table->dateTime('date_of_joining')->nullable();
            $table->dateTime('date_of_leaving')->nullable();
            $table->string('role_id')->nullable();
            $table->string('L1_user_id')->nullable();
            $table->string('L2_user_id')->nullable();
            $table->string('L3_user_id')->nullable();
            $table->string('department_code')->nullable();
            $table->string('vertical_code')->nullable();
            $table->string('functional_role')->nullable();
            $table->string('user_salary')->nullable();
            $table->string('is_sp')->nullable();
            $table->string('sp_name')->nullable();
            $table->string('sp_urnno')->nullable();
            $table->string('sp_code')->nullable();
            $table->string('sp_type')->nullable();
            $table->string('noc_issued')->nullable();
            $table->string('RBM')->nullable();
            $table->string('CBM')->nullable();
            $table->dateTime('sp_certificate_date')->nullable();
            $table->dateTime('certificate_valid_from')->nullable();
            $table->dateTime('certificate_valid_till')->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('user_additional_data');
    }
};
