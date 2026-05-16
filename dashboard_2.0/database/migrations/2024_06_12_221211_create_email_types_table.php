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
        if(!Schema::hasTable('email_types')) {
        Schema::create('email_types', function (Blueprint $table) {
            $table->id('type_id');
            $table->string('display_name');
            $table->string('value');
            $table->string('columns');
            $table->timestamps();
        });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('email_types');
    }
};
