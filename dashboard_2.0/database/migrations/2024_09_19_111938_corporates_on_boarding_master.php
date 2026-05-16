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
        schema::create('corporates_on_boarding_master', function (Blueprint $table) {
            $table->id();
            $table->string('first_name');
            $table->string('last_name');
            $table->string('company_name');
            $table->string('designation');
            $table->string('work_email');
            $table->integer('mobile_no');
            $table->string('no_of_employees');
            $table->enum('is_verified', ['Y', 'N'])->default('N');
            $table->string('is_verified_required_to')->nullable();
            $table->string('other_email')->nullable();
            $table->string('company_domain')->nullable();
            $table->timestamps();

        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('corporates_on_boarding_master');
    }
};
