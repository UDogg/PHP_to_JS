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
        Schema::table('corporates_on_boarding_master', function (Blueprint $table) {
            Schema::table('corporates_on_boarding_master', function (Blueprint $table) {
                $table->string('first_name')->nullable()->change();
                $table->string('last_name')->nullable()->change();
                $table->string('company_name')->nullable()->change();
                $table->string('designation')->nullable()->change();
                $table->string('work_email')->nullable()->change();
                $table->string('mobile_no')->nullable()->change();
                $table->string('no_of_employees')->nullable()->change();
                $table->enum('is_verified', ['Y', 'N'])->nullable()->default('N')->change();
                $table->string('is_verified_required_to')->nullable()->change();
                $table->string('other_email')->nullable()->change();
                $table->string('company_domain')->nullable()->change();
            });
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('corporates_on_boarding_master', function (Blueprint $table) {
            $table->string('first_name')->nullable(false)->change();
            $table->string('last_name')->nullable(false)->change();
            $table->string('company_name')->nullable(false)->change();
            $table->string('designation')->nullable(false)->change();
            $table->string('work_email')->nullable(false)->change();
            $table->integer('mobile_no')->nullable(false)->change();
            $table->string('no_of_employees')->nullable(false)->change();
            $table->enum('is_verified', ['Y', 'N'])->default('N')->change();
            $table->string('is_verified_required_to')->nullable(false)->change();
            $table->string('other_email')->nullable(false)->change();
            $table->string('company_domain')->nullable(false)->change();
        });
    }
};
